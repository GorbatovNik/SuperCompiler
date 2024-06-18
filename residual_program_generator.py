from sll_language import *
from algebra import *
from process_tree import *

class ProtoRule():
    def __init__(self, contr = {}, letCallList = [], bodyList = []):
        self.contr = contr
        self.letCallList = letCallList
        self.bodyList = bodyList

class advancedResidualProgramGenerator(object):
    def __init__(self, tree):
        self.tree = tree
        self.sigs = dict()
        self.rules = []

    def getSig(self, beta, name, vs):
        sig = self.sigs.get(beta, None)
        if sig:
            return sig
        else:
            name1 = "%s%s" % (name, len(self.sigs) + 1)
            sig1 = (name1, vs)
            self.sigs[beta] = sig1
            beta.residualName = name1
            return sig1

    def genResidualProgram(self):
        resExp = self.genExp(self.tree.root)
        return (Program(self.rules, ), resExp)
    
    def defineFormatParams(self, node):
        while len(node.children) == 1 and not node.children[0].contr and not node.exp.isPassive() and not node.exp.isLet() and node.isBase == Node.IsBase.FALSE:
            protos = self.defineFormatParams(node.children[0])
            node.protos = copy.deepcopy(protos)
            return node.protos

        if node.exp.isPassive():
            subst = matchAgainst(node.outFormat.exp, node.exp)
            if subst is None:
                protos = [ProtoRule()]
            else:
                protos = [ProtoRule(bodyList = [subst[vname] for vname in node.outFormat.exp.vars()])]
            node.protos = protos
            return protos

        if not node.exp.isLet():
            if node.isBase == Node.IsBase.TRUE:
                params = node.exp.vars()
                sig = self.getSig(node, node.exp.name, params)
            alpha = node.funcAncestor()
            if alpha:
                sig = self.sigs[alpha]
                if not equiv(node.outFormat.exp, alpha.outFormat.exp):
                    subst = matchAgainst(node.outFormat.exp, alpha.outFormat.exp)
                    letCall = LetCall(alpha.outFormat.exp.vars(), HCall(sig[0],[Var(vname) for vname in sig[1]]))
                    bodyList = []
                    for vname in node.outFormat.exp.vars():
                        bodyList.append(subst[vname])

                    resProtos = [ProtoRule(letCallList=[letCall], bodyList=bodyList)]
                else:
                    resProtos = [ProtoRule(bodyList=[HCall(sig[0],[Var(vname) for vname in sig[1]])])]
            else:
                resProtos = []
                for child in node.children:
                    protos = copy.deepcopy(self.defineFormatParams(child))

                    for proto in protos:
                        newContr = copy.deepcopy(child.contr)
                        for key, value in newContr.items():
                            newContr[key] = value.applySubst(proto.contr)
                        for key, value in proto.contr.items():
                            if key not in newContr:
                                newContr[key] = value
                        proto.contr = newContr
                        resProtos.append(proto)

            node.protos = resProtos
            if node.isBase == Node.IsBase.CANDIDATE and len(resProtos)>1:
                params = node.exp.vars()
                sig = self.getSig(node, node.exp.name, params)
            if node.isBase == Node.IsBase.TRUE or node.isBase == Node.IsBase.CANDIDATE and len(resProtos)>1:
                self.genAFunc(node)
                sig = self.sigs[node]
                node.protos = [ProtoRule(bodyList = [HCall(sig[0],[Var(vname) for vname in sig[1]])])]
            return node.protos
        
        assert node.exp.isLet()

        if node.children[-1].isBase != Node.IsBase.TRUE:
            node.children[-1].isBase = Node.IsBase.CANDIDATE
        inProto = copy.deepcopy(self.defineFormatParams(node.children[-1])[0]) # check in = let-node situation
        for (let, (i, (vname, _))) in zip(node.children[:-1], enumerate(node.exp.bindings)):
            if len(node.children)==0 or node.children[i].exp.isVar() or not node.exp.can_insert_format_to_body() or (node.children[i].outFormat.exp.isStackBottom() and node.exp.type != Let.Type.CTR_DECOMPOSE):
                if len(node.children)==0 or node.children[i].outFormat.exp.isStackBottom() or node.children[i].exp.isVar():
                    let.outFormat.exp = Var(vname)
            if let.isBase != Node.IsBase.TRUE:
                let.isBase = Node.IsBase.CANDIDATE
            protos = self.defineFormatParams(let)
            letBodyList = protos[0].bodyList
            callListToAdd = copy.deepcopy(protos[0].letCallList)
            # inProto.letCallList = inProto.letCallList + protos[0].letCallList
            inBodyList = inProto.bodyList

            if len(node.children)==0 or node.children[i].exp.isVar() or not node.exp.can_insert_format_to_body() or (node.children[i].outFormat.exp.isStackBottom() and node.exp.type != Let.Type.CTR_DECOMPOSE):
                if len(node.children)==0 or node.children[i].outFormat.exp.isStackBottom() or node.children[i].exp.isVar():
                    # lbl += f"{vname}:={str(exp)}, "
                    letSubst = {vname : letBodyList[0]}
                else:
                    # lbl += f"{vname}:={str(node.children[i].outFormat.exp)}, "
                    letSubst = {vname : let.outFormat.exp}
                for i in range(len(inBodyList)):
                    inBodyList[i] = inBodyList[i].applySubst(letSubst)
                for i in range(len(inProto.letCallList)):
                    inProto.letCallList[i].call = inProto.letCallList[i].call.applySubst(letSubst)
            if not let.exp.isVar() and (not let.outFormat.exp.isStackBottom() or node.exp.type == Let.Type.CTR_DECOMPOSE) and not (let.exp.isPassive() and not let.exp.hasVar()):
        #         lbl += f"&lt;{','.join(let.outFormat.exp.vars())}&gt;:=(({str(let.exp)}):{let.outFormat.exp}), "
                if len(letBodyList) == 1:
                    callListToAdd.append(LetCall(let.outFormat.exp.vars(), letBodyList[0]))
                else:
                    assert len(letBodyList) == len(let.outFormat.exp.vars())
                    for (vname, letBody) in zip(let.outFormat.exp.vars(), letBodyList):
                        callListToAdd.append(LetCall([vname], letBody))
            inProto.letCallList = callListToAdd + inProto.letCallList
        node.protos = [inProto]
        return node.protos

    def genAFunc(self, node, sig = None):
        params = node.exp.vars()
        sig = sig or self.getSig(node, node.exp.name, params)
        for proto in node.protos:
            patternList = []
            for param in params:
                if param in proto.contr:
                    patternList.append(proto.contr[param])
                else:
                    patternList.append(Var(param))
            letCallList = proto.letCallList
            bodyList = proto.bodyList
            arule = ARule(sig[0], patternList, letCallList, bodyList, len(node.outFormat.exp.vars()))
            self.rules.append(arule)

    def generate_scala(self):
        # self.tree.root.isBase = True
        self.defineFormatParams(self.tree.root)
        for proto in self.tree.root.protos:
            if len(proto.bodyList) == 1:
                proto.letCallList.append(LetCall(self.tree.root.outFormat.exp.vars(), proto.bodyList[0]))
            elif len(proto.bodyList) > 1:
                for (var, body) in zip(self.tree.root.outFormat.exp.vars(), proto.bodyList):
                    proto.letCallList.append(LetCall([var], body))
            proto.bodyList = [self.tree.root.outFormat.exp] if not self.tree.root.outFormat.exp.isStackBottom() else []
        

        mainsig = ("main", self.tree.root.exp.vars())
        self.sigs[self.tree.root] = mainsig
        self.genAFunc(self.tree.root, mainsig)
        self.tree.root.residualName = "main"

        ctrs = {}
        def ctrsTrawl(exp):
            if exp.isCtr():
                ctrs[exp.name] = len(exp.args)
            if exp.isCall():
                for arg in exp.args:
                    ctrsTrawl(arg)

        for rule in self.rules:
            for patt in rule.patternList:
                ctrsTrawl(patt)
            for letCall in rule.letCallList:
                ctrsTrawl(letCall.call)
            for body in rule.bodyList:
                ctrsTrawl(body)

        scala = ""
        for name, size in ctrs.items():
            scala += f"case object {name}" if size==0 else f"case class {name}("
            if size>0:
                scala += "x1 : Any"
                for i in range(size-1):
                    scala += f", x{i+2} : Any"
                scala += ")"
            scala+="\n"
        funcs = {}
        for rule in self.rules:
            if rule.name not in funcs:
                funcs[rule.name] = []
            funcs[rule.name].append(rule)

        def getAnySign(size):
            if size == 0:
                return "Unit"
            return "Any" if size == 1 else "(Any" + ", Any"*(size - 1) + ")"

        def getLeftSide(patternList):
            if len(patternList)==0:
                l = "()"
            elif len(patternList)==1:
                l = str(patternList[0])
            else:
                l = "(" + str(patternList[0])
                for i in range(len(patternList)-1):
                    l += ", " + str(patternList[i+1])
                l += ")"
            return l
        def getRightSide(letCallList, bodyList):
            def getBody(bodyList):
                if len(bodyList) == 0:
                    return ""
                    
                if len(bodyList) == 1:
                    r = str(bodyList[0])
                else:
                    r = "(" + str(bodyList[0])
                    for i in range(len(bodyList)-1):
                        r += ", " + str(bodyList[i+1])
                    r += ")"
                return r

            if len(letCallList)==0:
                r = getBody(bodyList)
            else:
                r = "{\n"
                for letCall in letCallList:
                    if len(letCall.params)==0:
                        r+="      " + str(letCall.call) + "\n"
                    else:
                        r += "      val "
                        if len(letCall.params) == 1:
                            r += str(letCall.params[0])
                        else:
                            r += "(" + str(letCall.params[0])
                            for i in range(len(letCall.params)-1):
                                r += ", " + str(letCall.params[i+1])
                            r += ")"
                        r += " = " + str(letCall.call) + "\n"
                r += "      " + getBody(bodyList) + "\n    }"
            return r

	
        # main_vars = self.tree.root.exp.vars()
        # rootsig = self.sigs[self.tree.root]
        # mainLetCall = LetCall(self.tree.root.outFormat.exp.vars(), GCall(rootsig[0], rootsig[1]))
        scala+="object Main {\n" #def main : " + getAnySign(len(main_vars)) + " => Any = {\n    case " + getLeftSide(main_vars) + " => " + getRightSide([mainLetCall], [self.tree.root.outFormat.exp]) + "\n  }\n"#+ str(self.tree.root.outFormat.exp.applySubst()) + "\n  }\n"
        
        for func_name, rules in funcs.items():
            scala+="  def " + func_name + " : " + getAnySign(len(rules[0].patternList)) + " => " + ("Any" if func_name=="main" else getAnySign(rules[0].outArity)) + " = {\n"
            for rule in rules:
                scala+="    case " + getLeftSide(rule.patternList) + " => " + getRightSide(rule.letCallList, rule.bodyList) + "\n"
            scala+="  }\n"
        scala+="}\n"
        return scala