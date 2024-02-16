# -*- coding: utf-8 -*-
'''
Created on Aug 20, 2009

@author: Sergei Romanenko
'''

from sll_language import *
from algebra import matchAgainst 
from process_tree import Contraction, Node, ProcessTree
import copy

class Solver:
    def __init__(self, driveEngine, nameGen):
        self.driveEngine = driveEngine
        self.nameGen = nameGen
        self.contractions = dict()
        self.subst = dict()
        self.isConsistentBool = True
        self.extraDriving = None
    
    def isConsistent(self):
        return self.isConsistentBool
    
    def addEquation(self, l, r):
        l = l.applySubst(self.contractions)
        
        if r.isVar():
            self.subst[r.vname] = l
        elif l.isCtr() and r.isCtr():
            if l.name == r.name:
                for larg, rarg in zip(l.args, r.args):
                    self.addEquation(larg, rarg)
                    if self.extraDriving:
                        return
            else:
                self.isConsistentBool = False
        elif l.isVar():
            def changeVarsToNewParams(e):
                if e.isVar():
                    freshName = self.nameGen.freshName()
                    result = [(e.vname[:], Var(freshName))]
                    e.vname = freshName
                elif e.isCtr():
                    result = []
                    for arg in e.args:
                        result = result + changeVarsToNewParams(arg)
                else:
                    raise ValueError('unexpected node in left side of rule met')
                
                return result

            r = copy.deepcopy(r)
            print(f"\nr before changing {r}")
            subst = dict(changeVarsToNewParams(r))
            print(f"r after changing {r}")
            print(f"new subst: {subst}")
            self.subst.update(subst)
            newCntr = dict([(l.vname, r)])
            for key in self.contractions.keys():
                self.contractions[key] = self.contractions[key].applySubst(newCntr)
            for key in self.subst.keys():
                self.subst[key] = self.subst[key].applySubst(newCntr)
            self.contractions[l.vname] = r
        
        elif l.isCall():
            self.extraDriving = self.driveEngine.drivingStep(l)
            print()
        else:
            raise ValueError('unknown situation')

class DrivingEngine(object):

    def __init__(self, nameGen, prog):
        "The program is supposed to be correct: no duplicate definitions, etc."
        self.nameGen = nameGen
        self.fRule = dict()
        self.gRules = dict()
        self.gcRule = dict()
        self.hRules = dict()
        for rule in prog.rules:
            name = rule.name
            if isinstance(rule, FRule):
                self.fRule[name] = rule
            elif isinstance(rule, GRule):
                if name in self.gRules:
                    "Lists are mutable!"
                    self.gRules[name].append(rule)
                else:
                    self.gRules[name] = [rule]
                self.gcRule[(rule.name, rule.cname)] = rule
            elif isinstance(rule, HRule):
                if name in self.hRules:
                    "Lists are mutable!"
                    self.hRules[name].append(rule)
                else:
                    self.hRules[name] = [rule]
            else:
                raise ValueError("Invalid rule")


# e : Exp (Var, Call, Let, Ctr)

# возвращает список выражений, на которые ветвится выражение e
    def drivingStep(self, e, checkContractionNeed=False):
        if e.isCtr():
            return False if checkContractionNeed else [(arg, None) for arg in e.args]
        elif e.isFCall():
            rule = self.fRule[e.name]
            p2a = dict(list(zip(rule.params, e.args)))
            body = rule.body.applySubst(p2a)
            return False if checkContractionNeed else [(body, None)]
        elif e.isGCall():
            arg0 = e.args[0]
            args = e.args[1:]
            if arg0.isCtr():
                cname = arg0.name
                cargs = arg0.args
                rule = self.gcRule[(e.name, cname)]
                p2a = dict()
                p2a.update(list(zip(rule.cparams, cargs)))
                p2a.update(list(zip(rule.params, args)))
                body = rule.body.applySubst(p2a)
                return False if checkContractionNeed else [(body, None)]
            elif arg0.isVar():
                rules = self.gRules[e.name]
                return True if checkContractionNeed else [ self.driveBranch(e, rule) for rule in rules ]
            else:
                branchesOrContrationNeed = self.drivingStep(arg0, checkContractionNeed)
                return branchesOrContrationNeed if checkContractionNeed else [ (GCall(e.name, [exp] + args), c) for (exp, c) in branchesOrContrationNeed]
        elif e.isHCall():
            res = []
            rules = self.hRules[e.name]
            for rule in rules:
                solver = Solver(self, self.nameGen)
                for k, (earg, rarg) in enumerate(zip(e.args, rule.patternList)):
                    solver.addEquation(earg, rarg)
                    solver_branches = solver.extraDriving
                    if solver_branches:
                        if checkContractionNeed:
                            return True
                        branches = []
                        for (subexp, c) in solver_branches:
                            newexp = e.applySubst(c)
                            newexp.args[k] = subexp
                            branches.append((newexp, c))
                        return branches 
                if solver.isConsistent():
                    res.append((rule.body.applySubst(solver.subst), solver.contractions))
                    if not solver.contractions:
                        if checkContractionNeed:
                            return len(res)>1
                        return res
            return len(res)>0 if checkContractionNeed else res
        elif e.isLet():
            return False if checkContractionNeed else [(e.body, None)] + [(exp, None) for (vn, exp) in e.bindings]
        else:
            raise ValueError("Unknown expression type")

    def driveBranch(self, e, rule):
        vname = e.args[0].vname
        cname = rule.cname
        cparams = self.nameGen.freshNameList(len(rule.cparams))
        params = rule.params
        cargs = [Var(vn) for vn in cparams]
        vname2ctr = dict([(vname, Ctr(cname, cargs))])
        e1 = e.applySubst(vname2ctr)
        branches = self.drivingStep(e1)
        e2 = branches[0][0]
        return (e2, Contraction(vname, cname, cparams))

class BasicProcessTreeBuilder(object):

    def __init__(self, drivingEngine, exp):
        self.drivingEngine = drivingEngine
        self.tree = ProcessTree(exp)

    # The parts common to the basic and advanced supercompilers.

    # If beta `instOf` alpha, we generalize beta by introducing
    # a let-expression, in order to make beta the same as alpha
    # (modulo variable names).

    def loopBack(self, beta, alpha):
        subst = matchAgainst(alpha.exp, beta.exp)
        bindings = list(subst.items())
        bindings.sort()
        letExp = Let(alpha.exp, bindings)
        self.tree.replaceSubtree(beta, letExp)

    # This function applies a driving step to the node's expression,
    # and, in general, adds children to the node.

    def expandNode(self, beta):
        branches = self.drivingEngine.drivingStep(beta.exp)
        self.tree.addChildren(beta, branches)

    # Basic supercompiler process tree builder

    def buildStep(self, beta):
        """
        This method is overridden in the advanced version of
        the process tree builder.
        """
        alpha = beta.findMoreGeneralAncestor()
        if alpha:
            self.loopBack(beta, alpha)
        else:
            self.expandNode(beta)

    def buildProcessTree(self, k):
        # Specifying k = -1 results in an unlimited building loop.
        while True:
            if k == 0:
                break
            k -= 1
            beta = self.tree.findUnprocessedNode()
            print(beta)
            if not beta:
                break
            self.buildStep(beta)

def buildBasicProcessTree(nameGen, k, prog, exp):
    drivingEngine = DrivingEngine(nameGen, prog)
    builder = BasicProcessTreeBuilder(drivingEngine, exp)
    builder.buildProcessTree(k)
    return builder.tree