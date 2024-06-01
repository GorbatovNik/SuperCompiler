from sll_language import *
from algebra import *
from graphviz import Digraph

class Contraction(object):
    def __init__(self, vname, cname, cparams):
        self.vname = vname
        self.cname = cname
        self.cparams = cparams

    def __str__(self):
        cparams_s = ",".join(self.cparams)
        pat_s = self.cname
        if len(self.cparams) > 0 :
            pat_s += "(" + cparams_s + ")"
        return self.vname + "=" + pat_s

def showNodeId(node):
    if node :
        return node.nodeId
    else:
        return None

class Node(object):
    "The constructor is supposed to be called via ProcessTree#newNode only."
    
    def __init__(self, tree, exp, contr, parent, children, drivingFuncName=None, outFormat = None):
        "nodeId is only used for unit testing purposes"
        self.nodeId = tree.getFreshNodeId()
        self.exp = exp
        self.contr = contr
        self.parent = parent
        self.children = children
        self.drivingFuncName = drivingFuncName
        self.outFormat = outFormat
        self.isLast = False
        if outFormat is None:
            self.outFormat = OutFormat(self, self)

    def __str__(self):
        children_s = ",".join(["%s" % n.nodeId for n in self.children])
        contr = None
        if isinstance(self.contr, Contraction):
            contr = str(self.contr)
        elif self.contr is not None:
            contr = "{"
            for key,value in self.contr.items():
                contr += f"\'{key}\': " + str(value) +", "
            contr += "}"
        return "%s:(%s,%s,%s,%s[%s])" % (self.nodeId, self.exp,
                                     contr, showNodeId(self.parent), self.outFormat.exp,
                                     children_s)

    def convertToDOT(self, dot, parentEdgeLabel= None):
        color = "blue" if self.isLast else "black"
        dot.node(str(self.nodeId), "<(" + str(self.exp) + "):" + str(self.outFormat.exp) + "<br/>DFN = " + str(self.drivingFuncName) + "<br/>exp_type = " + str(type(self.exp).__name__) + ">", color = color)
        if self.isLeaf():
            anc = self.funcAncestor()
            if anc:
                dot.edge(str(self.nodeId), str(anc.nodeId), style="dashed")

        if self.parent:
            dot.edge(str(self.parent.nodeId), str(self.nodeId), label=parentEdgeLabel)
        for i, child in enumerate(self.children):
            if self.exp.isLet():
                label = "in" if i==0 else "let"
            else:
                label = ('\n'.join([str(key) + "→" + str(value) for key, value in child.contr.items()])) if child.contr is not None else ""
            child.convertToDOT(dot, label)

    def ancestors(self):
        n = self.parent
        while n:
            yield n
            n = n.parent

    def funcAncestor(self):
        for n in  self.ancestors():
            if equiv(self.exp, n.exp): # с точностью до имен переменных
                return n
        return None
    

    def findMoreGeneralAncestor(self): 
        for n in self.ancestors():
            if n.exp.isFGHCall() and instOf(self.exp, n.exp): # с точностью до имен переменных
                return n
        return None
    

    def isProcessed(self):
        if self.exp.isVar():
            return True
        elif self.exp.isCtr():
            return self.exp.args == []
        elif self.exp.isFGHCall():
            return self.funcAncestor() != None
        elif self.exp.isLet():
            return False
        else:
            raise ValueError("Invalid exp")

    def subtreeNodes(self):
        yield self
        for child in self.children:
            for n in child.subtreeNodes():
                yield n

    def isLeaf(self):
        return self.children == []

    def subtreeLeaves(self):
        if self.isLeaf():
            yield self
            return
        for child in self.children:
            for n in child.subtreeLeaves():
                yield n

class ProcessTree(object):
    "NB: The tree is not functional, since its nodes are updated in place."

    def __init__(self, exp):
        self.freshNodeId = -1
        self.root = self.newNode(exp, None, None, [])
        
    def __str__(self):
        nodes_s = ",".join(["%s" % n for n in self.nodes()])
        return "{%s}" % nodes_s
    
    def convertToDOT(self):
        dot = Digraph()
        dot.node_attr.update(fontname='DejaVu Sans Mono')
        dot.edge_attr.update(fontname='DejaVu Sans Mono')
        self.root.convertToDOT(dot)
        return dot

    def getFreshNodeId(self):
        self.freshNodeId += 1
        return self.freshNodeId

    def newNode(self, exp, contr, parent, children, drivingFuncName = None, outFormat = None):
        return Node(self, exp, contr, parent, children, drivingFuncName=drivingFuncName, outFormat = None)

    def nodes(self):
        for n in self.root.subtreeNodes():
            yield n

    def leaves(self):
        "Here, the tree is supposed not to be empty."
        for n in self.root.subtreeLeaves():
            yield n

    def findUnprocessedNode(self):
        for n in self.leaves():
            if not n.isProcessed():
                return n
        return None

    def isFuncNode(self, node):
        for leaf in self.leaves():
            if node == leaf.funcAncestor():
                return True
        return False

    def addChildren(self, node, branches):
        children = [self.newNode(exp, contr, node, [], drivingFuncName=drivingFuncName) for (exp, contr, drivingFuncName) in branches]
        node.children += children

    def replaceSubtree(self, node, exp):
        node.children = []
        node.exp = exp
