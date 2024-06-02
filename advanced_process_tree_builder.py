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

        alpha.isLast = True
        dot = self.tree.convertToDOT()
        dot.render("dangerous embdding managed", view=True)
        alpha.isLast = False

    def split(self, beta):

        exp = beta.exp
        args = exp.args
        names1 = self.nameGen.freshNameList(len(args))
        args1 = [Var(x) for x in names1]
        letExp = Let(beta.exp.cloneFunctor(args1), list(zip(names1, args)))
        self.tree.replaceSubtree(beta, letExp)

        beta.isLast = True
        dot = self.tree.convertToDOT()
        dot.render("dangerous embdding managed", view=True)
        beta.isLast = False

    def generalizeAlphaOrSplit(self, beta, alpha):
        # print('before generalizing:--------\n ' + str(self.tree) +"\n--------------------")
        gen = self.msgBuilder.build(alpha.exp, beta.exp)
        beta.isLast = True
        alpha.isLast = True
        dot = self.tree.convertToDOT()
        dot.render("dangerous embdding found. msg = " + str(gen.exp), view=True)
        beta.isLast = False
        alpha.isLast = False

        if gen.exp.isVar():
            self.split(beta)
            return beta
        else:
            self.abstract(alpha, gen.exp, gen.substA)
            return alpha

    def findEmbeddedAncestor(self, beta, contractionNeed, drivingFuncName):
        for alpha in beta.ancestors():
            alphaContractionNeed = bool(alpha.children[0].contr)
            if alpha.exp.isFGHCall() and alphaContractionNeed == contractionNeed and alpha.drivingFuncName==drivingFuncName and embeddedIn(alpha.exp, beta.exp):
                return alpha
        return None
    
    def findAsSpecCaseEmbeddedAncestor(self, beta):
        for alpha in beta.ancestors():
            if embeddedIn(alpha.exp, beta.exp, asSpecialCase=True):
                return alpha

    def buildStep(self, beta):
        alpha = beta.findMoreGeneralAncestor()
        # alpha = self.findAsSpecCaseEmbeddedAncestor(beta)
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

    def manageLet(self, node):
        self.expandNode(node)
        for child in node.children[:-1]:
            self.buildRecursive(child)
        
    def buildRecursive(self, beta):
        print(beta.exp)
        if beta.isPassive():
            if beta.outFormat.exp.isStackBottom():
                
                beta.isLast = True
                dot = self.tree.convertToDOT()
                dot.render("Hypothesis is refuted", view=True)
                beta.isLast = False

                newfmt = copy.deepcopy(beta.exp)
                newfmt.changeVarsToNewParams(self.nameGen)
                root = beta.outFormat.root
                root.outFormat.exp = newfmt
                root.children = []

                root.isLast = True
                dot = self.tree.convertToDOT()
                dot.render("New format hypothesis", view=True)
                root.isLast = False
                
                self.buildRecursive(root)
            else:
                mg = matchAgainst(beta.outFormat.exp, beta.exp)
                if mg is None:
                    gen = self.msgBuilder.build(beta.outFormat.exp, beta.exp)
                    
                    beta.isLast = True
                    dot = self.tree.convertToDOT()
                    dot.render("Hypothesis is refuted", view=True)
                    beta.isLast = False

                    root = beta.outFormat.root
                    root.outFormat.exp = gen.exp
                    root.children = []

                    root.isLast = True
                    dot = self.tree.convertToDOT()
                    dot.render("New format hypothesis", view=True)
                    root.isLast = False

                    self.buildRecursive(root)
            return
        if beta.isProcessed() and beta.exp.isFGHCall():
            anc = beta.funcAncestor()
            if anc:
                if not anc.outFormat.exp.isStackBottom():
                    if beta.outFormat.exp.isStackBottom():
                        beta.isLast = True
                        anc.isLast = True
                        dot = self.tree.convertToDOT()
                        dot.render("Hypothesis is refuted", view=True)
                        beta.isLast = False
                        anc.isLast = False

                        root = beta.outFormat.root
                        root.outFormat.exp = copy.deepcopy(anc.outFormat.exp)
                        root.children = []

                        root.isLast = True
                        dot = self.tree.convertToDOT()
                        dot.render("New format hypothesis", view=True)
                        root.isLast = False

                        self.buildRecursive(root)

                        return
                    else:
                        mg = matchAgainst(beta.outFormat.exp, anc.outFormat.exp)
                        if not mg:
                            gen = self.msgBuilder.build(beta.outFormat.exp, anc.outFormat.exp)

                            beta.isLast = True
                            anc.isLast = True
                            dot = self.tree.convertToDOT()
                            dot.render("Hypothesis is refuted", view=True)
                            beta.isLast = False
                            anc.isLast = False

                            root = beta.outFormat.root
                            root.outFormat.exp = gen.exp
                            root.children = []

                            root.isLast = True
                            dot = self.tree.convertToDOT()
                            dot.render("New format hypothesis", view=True)
                            root.isLast = False

                            self.buildRecursive(root)

                            return
            return
        if beta.isProcessed():
            return
        moreGenAnc = beta.findMoreGeneralAncestor()
        if moreGenAnc:
            self.loopBack(beta, moreGenAnc) # beta.exp is let now
            self.manageLet(beta)
        else:
            if not beta.exp.isCtr():
                contrNeed = self.drivingEngine.drivingStep(beta.exp, checkContractionNeed=True)
                alpha = self.findEmbeddedAncestor(beta, contrNeed, beta.drivingFuncName)
                if alpha:
                    # print("embeding found\nbeta=%s\nalpha=%s" % (beta, alpha))
                    node = self.generalizeAlphaOrSplit(beta, alpha)
                    self.manageLet(node)
                    return
            if beta.exp.isLet():
                self.manageLet(node)
                return
            self.expandNode(beta)
            for child in beta.children:
                self.buildRecursive(child)

def buildAdvancedProcessTree(nameGen, k, prog, exp):
    drivingEngine = DrivingEngine(nameGen, prog)
    builder = AdvancedProcessTreeBuilder(drivingEngine, exp)
    # builder.buildProcessTree(k)
    builder.buildRecursive(builder.tree.root)
    return builder.tree
