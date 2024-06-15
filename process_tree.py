from sll_language import *
from algebra import *
from ge import *
from graphviz import Digraph
import shutil
import os
import global_vars

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
        self.isBase = False
        if outFormat is None:
            self.outFormat = OutFormat(self, self)

    def __str__(self):
        children_s = ",".join(["%s" % n.nodeId for n in self.children])
        contr = None
        if self.contr is not None:
            contr = "{"
            for key,value in self.contr.items():
                contr += f"\'{key}\': " + str(value) +", "
            contr += "}"
        return "%s:(%s,%s,%s,%s[%s])" % (self.nodeId, self.exp,
                                     contr, showNodeId(self.parent), self.outFormat.exp,
                                     children_s)

    def ancestors(self):
        n = self.parent
        while n:
            yield n
            n = n.parent

    def funcAncestor(self):
        for n in  self.ancestors():
            if equiv(self.exp, n.exp) and self.exp.vars() == n.exp.vars():
                return n
        return None
    

    def findMoreGeneralAncestor(self): 
        for n in self.ancestors():
            if n.exp.isFGHCall() and instOf(self.exp, n.exp): # с точностью до имен переменных
                return n
        return None
    
    def findMoreGeneralEmbeddedAncestor(self, freshName):
        for n in self.ancestors():
            if n.exp.isFGHCall():
                (C, Cz) = moreGeneralEmbeddedIn(n.exp, self.exp, freshName)
                if C:
                    return n, C, Cz
        return None, None, None
    
    def isPassive(self):
        return self.exp.isPassive()

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

def reset_folder(folder_path):
    shutil.rmtree(folder_path, ignore_errors=True)
    os.makedirs(folder_path, exist_ok=True)

class ProcessTree(object):
    "NB: The tree is not functional, since its nodes are updated in place."

    def __init__(self, exp):
        self.freshNodeId = -1
        self.root = self.newNode(exp, None, None, [])
        self.stats = {}
        self.tick = 1
        reset_folder("progress")

    def buildDot(self, node, dot, nodesToFocus, focusColor, parentEdgeLabel=None):
        color = focusColor if node in nodesToFocus else "black"
        if node.exp.isLet():
            lbl = "<(let "
            for (let, (vname, _)) in zip(node.children[:-1], node.exp.bindings):
                if not let.exp.isVar() and (not let.outFormat.exp.isStackBottom() or node.exp.type == Let.Type.CTR_DECOMPOSE) and not (let.exp.isPassive() and not let.exp.hasVar()):
                    lbl += f"&lt;{','.join(let.outFormat.exp.vars())}&gt;:=(({str(let.exp)}):{let.outFormat.exp}), "
            if len(lbl) > 7:
                lbl += "<br/>"
            for (i, (vname, exp)) in enumerate(node.exp.bindings):
                if len(node.children)==0 or node.children[i].exp.isVar() or not node.exp.can_insert_format_to_body() or (node.children[i].outFormat.exp.isStackBottom() and node.exp.type != Let.Type.CTR_DECOMPOSE):
                    if len(node.children)==0 or node.children[i].outFormat.exp.isStackBottom() or node.children[i].exp.isVar():
                        lbl += f"{vname}:={str(exp)}, "
                    else:
                        lbl += f"{vname}:={str(node.children[i].outFormat.exp)}, "
            if len(node.children) > 0:
                lbl += f"<br/>in {node.children[-1].exp}):{node.outFormat.exp}<br/>{node.exp.type.name}>"
            else:
                lbl += f"<br/>in {node.exp.body}):{node.outFormat.exp}<br/>{node.exp.type.value}>"
        else:
            lbl = "<(" + str(node.exp) + "):" + str(node.outFormat.exp) + "<br/>DFN = " + str(node.drivingFuncName) + ">"
        dot.node(str(node.nodeId), lbl, color = color)
        if node.isLeaf():
            anc = node.funcAncestor()
            if anc:
                dot.edge(str(node.nodeId), str(anc.nodeId), style="dashed")

        if node.parent:
            dot.edge(str(node.parent.nodeId), str(node.nodeId), label=parentEdgeLabel)
        for i, child in enumerate(node.children):
            if node.exp.isLet():
                label = "let" if i<len(node.children)-1 else "in"
            else:
                label = ('\n'.join([str(key) + "→" + str(value) for key, value in child.contr.items()])) if child.contr is not None else ""
            self.buildDot(child, dot, nodesToFocus, focusColor, label)

    def render(self, title, nodesToFocus = [], focusColor = 'blue', release=False):
        if not global_vars.debug and not release:
            return
        dot = Digraph()
        dot.node_attr.update(fontname='Sans Not-Rotated 14')
        dot.edge_attr.update(fontname='Sans Not-Rotated 14')
        self.buildDot(self.root, dot, nodesToFocus, focusColor)
        dot.attr(label=title, labelloc="t", fontsize="20")
        # dot.save(f'progress/{str(self.tick)}_{title}.jpg',)
        dot.render(f'progress/{f"{self.tick:05}"}_{title}', view = False)
        self.tick += 1

    def __str__(self):
        nodes_s = ",".join(["%s" % n for n in self.nodes()])
        return "{%s}" % nodes_s

    def getFreshNodeId(self):
        self.freshNodeId += 1
        return self.freshNodeId

    def newNode(self, exp, contr, parent, children, drivingFuncName = None, outFormat = None):
        return Node(self, exp, contr, parent, children, drivingFuncName=drivingFuncName, outFormat=outFormat)

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
        assert not node.exp.isCtr()
        if node.exp.isFGHCall():
            children = [self.newNode(exp, contr, node, [], drivingFuncName=drivingFuncName, outFormat=node.outFormat) for (exp, contr, drivingFuncName) in branches]
        elif node.exp.isLet():
            children = [self.newNode(exp, contr, node, [], drivingFuncName) for (exp, contr, drivingFuncName) in branches[:-1]] +\
                       [self.newNode(branches[-1][0], branches[-1][1], node, [], branches[-1][2], node.outFormat)]
        
        node.children += children

    def replaceSubtree(self, node, exp):
        node.children = []
        node.exp = exp
