### Advanced Supercompiler with homeomorphic imbedding and generalization  

from he import embeddedIn
from msg import MSGBuilder
from algebra import *
from sll_language import *
from process_tree import  Node, ProcessTree
import copy

class DrivingEngine(object):
    def __init__(self, nameGen, prog):
        "The program is supposed to be correct: no duplicate definitions, etc."
        self.nameGen = nameGen
        self.hRules = dict()
        for rule in prog.rules:
            name = rule.name
            if name in self.hRules:
                "Lists are mutable!"
                self.hRules[name].append(rule)
            else:
                self.hRules[name] = [rule]
    def drivingFCall(self, e, checkContractionNeed=False): #, node=None):
        if e.isCtr():
            return False if checkContractionNeed else [(arg, None, None) for arg in e.args]
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
                            return not(len(solver_branches)==1 and not solver_branches[0][1]) # solver_branches[0][1] is contraction
                        branches = []
                        for (subexp, c, drivingFuncName) in solver_branches:
                            newexp = e.applySubst(c)
                            newexp.args[k] = subexp
                            branches.append((newexp, c, drivingFuncName))
                        return branches 
                if solver.isConsistent():
                    res.append((rule.body.applySubst(solver.subst), solver.contractions, e.name))
                    # print(f"({str(res[-1][0])}, {str(res[-1][1])}, {str(res[-1][2])}")
                    if not solver.contractions:
                        if checkContractionNeed:
                            return len(res)>1
                        return res
            return len(res)>0 if checkContractionNeed else res

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
                for k, (larg, rarg) in enumerate(zip(l.args, r.args)):
                    self.addEquation(larg, rarg)
                    if self.extraDriving:
                        branches = []
                        for (subexp, c, drivingFuncName) in self.extraDriving:
                            newexp = l.applySubst(c)
                            newexp.args[k] = subexp
                            branches.append((newexp, c, drivingFuncName))
                        self.extraDriving = branches
                        return
            else:
                self.isConsistentBool = False
        elif l.isVar():
            r = copy.deepcopy(r)
            subst = dict(r.changeVarsToNewParams(self.nameGen))
            self.subst.update(subst)
            newCntr = dict([(l.vname, r)])
            for key in self.contractions.keys():
                self.contractions[key] = self.contractions[key].applySubst(newCntr)
            for key in self.subst.keys():
                self.subst[key] = self.subst[key].applySubst(newCntr)
            self.contractions[l.vname] = r
        
        elif l.isCall():
            self.extraDriving = self.driveEngine.drivingFCall(l)
            # print()
        else:
            raise ValueError('unknown situation')

class AdvancedProcessTreeBuilder(object):

    def __init__(self, drivingEngine, exp):
        self.drivingEngine = drivingEngine
        self.tree = ProcessTree(exp)
        self.nameGen = drivingEngine.nameGen
        self.msgBuilder = MSGBuilder(self.nameGen)

    def loopBack(self, beta, alpha):
        self.tree.render("Special case found", [beta, alpha])
        subst = matchAgainst(alpha.exp, beta.exp)
        bindings = list(subst.items())
        bindings.sort()
        letExp = Let(alpha.exp, bindings)
        self.tree.replaceSubtree(beta, letExp)
        beta.exp.type = "special case"
        # self.tree.render("Let-node for special case created", [beta])

    def abstract(self, alpha, exp, subst):
        bindings = list(subst.items())
        bindings.sort()
        letExp = Let(exp, bindings)
        # print(str(self.tree))
        self.tree.replaceSubtree(alpha, letExp)
        alpha.exp.type = "he: abstract"
        self.tree.render("dangerous embedding managed", [alpha])
        self.manageLet(alpha, False)

    def split(self, beta):
        exp = beta.exp
        args = exp.args
        names1 = self.nameGen.freshNameList(len(args))
        args1 = [Var(x) for x in names1]
        letExp = Let(beta.exp.cloneFunctor(args1), list(zip(names1, args)))
        self.tree.replaceSubtree(beta, letExp)
        beta.exp.type = "he: split"
        self.tree.render("dangerous embedding managed", [beta])
        self.manageLet(beta, True)

    def generalizeAlphaOrSplit(self, beta, alpha):
        gen = self.msgBuilder.build(alpha.exp, beta.exp)
        self.tree.render(f"dangerous embedding found. msg = {str(gen.exp)}", [alpha, beta])
        if gen.exp.isVar():
            self.split(beta)
        else:
            self.abstract(alpha, gen.exp, gen.substA)

    def findEmbeddedAncestor(self, beta, contractionNeed, drivingFuncName):
        for alpha in beta.ancestors():
            alphaContractionNeed = bool(alpha.children[0].contr)
            if alpha.exp.isFGHCall() and alphaContractionNeed == contractionNeed and alpha.drivingFuncName==drivingFuncName and embeddedIn(alpha.exp, beta.exp):
                return alpha
        return None

    def manageLet(self, node, insertFmtToIn):
        node.exp.insertFmtToIn = insertFmtToIn
        self.tree.render("Start let-node managing", [node])
        children = [(exp, None, None) for (vn, exp) in node.exp.bindings] + [(node.exp.body, None, node.drivingFuncName)]
        self.tree.addChildren(node, children)
        in_ = node.children[-1]
        newBinds = []
        bodySubst = {}
        for i, child in enumerate(node.children[:-1]):
            self.buildRecursive(child)
            if not child.outFormat.exp.isStackBottom() and not child.exp.isVar():
                if insertFmtToIn:
                    bodySubst[node.exp.bindings[i][0]] = child.outFormat.exp
                # else:
                newBinds.append((node.exp.bindings[i][0], child.outFormat.exp))
            else:
                newBinds.append(node.exp.bindings[i])
        node.exp.bindings = newBinds
        if insertFmtToIn:
            node.exp.body = node.exp.body.applySubst(bodySubst)
            in_.exp = copy.deepcopy(node.exp.body)
        self.tree.render("let-branches managed", [node])
        self.buildRecursive(in_)
        self.tree.render("in-branch managed", [node])
 
    def buildRecursive(self, beta):
        # print(beta.exp)
        if beta.isPassive():
            if beta.outFormat.exp.isStackBottom():
                self.tree.render("Hypothesis is refuted", [beta], focusColor='red')
                newfmt = copy.deepcopy(beta.exp)
                newfmt.changeVarsToNewParams(self.nameGen)
                root = beta.outFormat.root
                root.outFormat.exp = newfmt
                root.children = [] 
                self.tree.render("New format hypothesis", [root])
                self.buildRecursive(root)
            else:
                mg = matchAgainst(beta.outFormat.exp, beta.exp)
                if mg is None:
                    gen = self.msgBuilder.build(beta.outFormat.exp, beta.exp)
                    self.tree.render("Hypothesis is refuted", [beta], focusColor='red')
                    root = beta.outFormat.root
                    root.outFormat.exp = gen.exp
                    root.children = []
                    self.tree.render("New format hypothesis", [root])

                    self.buildRecursive(root)
            return
        if beta.isProcessed():
            alpha = beta.funcAncestor()
            if not alpha.outFormat.exp.isStackBottom():
                if beta.outFormat.exp.isStackBottom() or not equiv(beta.outFormat.exp, alpha.outFormat.exp):
                    self.tree.render("Hypothesis is refuted", [beta], focusColor='red')
                    newfmt = copy.deepcopy(alpha.outFormat.exp)
                    newfmt.changeVarsToNewParams(self.nameGen)
                    root = beta.outFormat.root
                    root.outFormat.exp = newfmt
                    root.children = []
                    self.tree.render("New format hypothesis", [root])
                    self.buildRecursive(root)
            return
        if beta.exp.isFGHCall():
            moreGenAnc = beta.findMoreGeneralAncestor() #FGHCall only
            if moreGenAnc:
                self.loopBack(beta, moreGenAnc) # beta.exp is let now
                self.manageLet(beta, False)
                return
        if beta.exp.isCtr():
            e = beta.exp
            names = self.nameGen.freshNameList(len(e.args))
            args = [Var(x) for x in names]
            letExp = Let(e.cloneFunctor(args), list(zip(names, e.args)))
            self.tree.replaceSubtree(beta, letExp)
            beta.exp.type = "ctr decompose"
            self.manageLet(beta, True)
            return
        
        if beta.exp.isFGHCall():
            freshName = self.nameGen.freshName()
            Cf, C, Cz = beta.findMoreGeneralEmbeddedAncestor(freshName) #FGHCall only
            if Cf:
                self.tree.render("More General Embedded Ancestor found", [beta, Cf])
                letExp = Let(Cz, [(freshName, C)])
                self.tree.replaceSubtree(beta, letExp)
                beta.exp.type = "general emb"
                self.tree.render("Let created", [beta, Cf])
                self.manageLet(beta, True)
                return
            
        contrNeed = beta.exp.isFGHCall() and self.drivingEngine.drivingFCall(beta.exp, checkContractionNeed=True)
        if beta.exp.isFGHCall():
            alpha = self.findEmbeddedAncestor(beta, contrNeed, beta.drivingFuncName)
            if alpha:
                self.generalizeAlphaOrSplit(beta, alpha)
                return
        if beta.exp.isFGHCall():
            children = self.drivingEngine.drivingFCall(beta.exp)
            self.tree.addChildren(beta, children)
            for child in beta.children:
                self.buildRecursive(child)
            return
        if beta.exp.isLet():
            self.manageLet(beta, beta.exp.insertFmtToIn)
            return
        assert False

def buildAdvancedProcessTree(nameGen, k, prog, exp):
    drivingEngine = DrivingEngine(nameGen, prog)
    builder = AdvancedProcessTreeBuilder(drivingEngine, exp)
    builder.buildRecursive(builder.tree.root)
    return builder.tree
