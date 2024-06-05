### Advanced Supercompiler with homeomorphic imbedding and generalization  

from basic_process_tree_builder import *
from he import embeddedIn
from msg import MSGBuilder
from algebra import *

class AdvancedProcessTreeBuilder(BasicProcessTreeBuilder):

    def __init__(self, drivingEngine, exp):
        self.drivingEngine = drivingEngine
        self.tree = ProcessTree(exp)
        self.nameGen = drivingEngine.nameGen
        self.msgBuilder = MSGBuilder(self.nameGen)

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

    def buildStep(self, beta):
        alpha = beta.findMoreGeneralAncestor()
        if alpha:
            self.loopBack(beta, alpha)
        else:
            if not beta.exp.isCtr():
                contrNeed = self.drivingEngine.drivingStep(beta.exp, checkContractionNeed=True)
                alpha = self.findEmbeddedAncestor(beta, contrNeed, beta.drivingFuncName)
                if alpha:
                    # print("embeding found\nbeta=%s\nalpha=%s" % (beta, alpha))
                    self.generalizeAlphaOrSplit(beta, alpha)
                else:
                    self.expandNode(beta)
            else:
                self.expandNode(beta)

    def manageLet(self, node, insertFmtToIn):
        node.exp.insertFmtToIn = insertFmtToIn
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
        self.buildRecursive(in_)
        self.tree.render("let managed", [node])
 
    def buildRecursive(self, beta):
        print(beta.exp)
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
        # if beta.exp.isLet():
        #     self.manageLet(node)
        #     return
        # self.expandNode(beta)
        # for child in beta.children:
        #     self.buildRecursive(child)

def buildAdvancedProcessTree(nameGen, k, prog, exp):
    drivingEngine = DrivingEngine(nameGen, prog)
    builder = AdvancedProcessTreeBuilder(drivingEngine, exp)
    # builder.buildProcessTree(k)
    builder.buildRecursive(builder.tree.root)
    return builder.tree
