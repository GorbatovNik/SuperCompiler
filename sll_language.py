import string
import copy
from enum import Enum

class Exp(object):
    def __ne__(self, other):
        result = self.__eq__(other)
        if result is NotImplemented:
            return result
        return not result
    def isVar(self):
        return False
    def isCall(self):
        return False
    def isCtr(self):
        return False
    def isFCall(self):
        return False
    def isGCall(self):
        return False
    def isHCall(self):
        return False
    def isFGHCall(self):
        return self.isFCall() or self.isGCall() or self.isHCall()
    def isLet(self):
        return False
    def isStackBottom(self):
        return False
    def hasTheSameFunctorAs(self, other):
        return False
    def isPassive(self):
        if self.isVar() or self.isStackBottom():
            return True
        if self.isCtr():
            ans = True
            for arg in self.args:
                ans = ans and arg.isPassive()
            return ans
        if self.isStackBottom():
            return True
        return False
    def hasStackBottom(self):
        if self.isStackBottom():
            return True
        if self.isCall():
            for arg in self.args:
                if arg.hasStackBottom():
                    return True
            return False
        return False
    
    def hasVar(self):
        if self.isVar():
            return True
        if self.isCall():
            for arg in self.args:
                if arg.hasVar():
                    return True
            return False
        return False
    def changeVarsToNewParams(self, nameGen):
        if self.isVar():
            freshName = nameGen.freshName()
            result = [(self.vname[:], Var(freshName))]
            self.vname = freshName
        elif self.isCtr():
            result = []
            for arg in self.args:
                result = result + arg.changeVarsToNewParams(nameGen)
        else:
            raise ValueError('unexpected node in left side of rule met')
        
        return result

class Var(Exp):
    def __init__(self, vname):
        self.vname = vname
    def __str__(self):
        return self.vname
    def __eq__(self, other):
        if not isinstance(other, Exp):
            return NotImplemented
        if other.isVar():
            return self.vname == other.vname
        else:
            return False
    def isVar(self):
        return True
    def applySubst(self, subst):
        return subst.get(self.vname, self)
    def vars(self):
        return [self.vname]

class Call(Exp):
    def __init__(self, name, args):
        self.name = name
        self.args = args
    def __str__(self):
        args_s = ", ".join(["%s" % e for e in self.args])
        return "%s(%s)" % (self.name, args_s)
    def __eq__(self, other):
        if not isinstance(other, Exp):
            return NotImplemented
        if self.__class__ is other.__class__:
            return self.name == other.name and self.args == other.args
        else:
            return False
    def isCall(self):
        return True
    def hasTheSameFunctorAs(self, other): 
        return (self.__class__ is other.__class__ 
                and self.name == other.name) # нет проверки на число аргументов
    def applySubst(self, subst):
        newCall = copy.copy(self)
        newCall.args = [ e.applySubst(subst) for e in self.args]
        return newCall
    def cloneFunctor(self, newArgs):
        newCall = copy.copy(self)
        newCall.args = newArgs
        return newCall
    def vars(self):
        '''
        We don't use sets here, in order to preserve
        the original order of variables in the expression.
        (The order is preserved just for readability of
        residual programs.)
        '''
        vs = []
        for arg in self.args:
            for v in arg.vars():
                if v not in vs:
                    vs.append(v)
        return vs

class Let(Exp):
    class Type(Enum):
        SPECIAL_CASE = "special case"
        HE_ABSTRACT = "homeo-emb: ancestor abstract"
        HE_SPLIT = "homeo-emb: descendant decompose"
        CTR_DECOMPOSE = "ctr decompose"
        GENERAL_EMB = "general emb"
    def __init__(self, body, bindings, type_):
        self.body = body
        self.bindings = bindings
        self.type = type_
    def __str__(self):
        # bindings_s = ",".join(["%s:=%s" % b for b in self.bindings])
        # return "let %s in %s" % (bindings_s, self.body)
        return "letexp"
    
    def vars(self):
        return [bind[0] for bind in self.bindings]
    
    def can_insert_format_to_body(self) -> bool:
        return self.type in [Let.Type.GENERAL_EMB, Let.Type.CTR_DECOMPOSE, Let.Type.HE_SPLIT]
    def isLet(self):
        return True

class Ctr(Call):
    def __init__(self, name, args):
        Call.__init__(self, name, args)
    def __str__(self):
        if len(self.args) == 0:
            return self.name
        else:
            return Call.__str__(self)
    def isCtr(self):
        return True

class FCall(Call):
    def __init__(self, name, args):
        Call.__init__(self, name, args)
    def isFCall(self):
        return True

class GCall(Call):
    def __init__(self, name, args):
        Call.__init__(self, name, args)
    def isGCall(self):
        return True
    
class HCall(Call):
    def __init__(self, name, args):
        Call.__init__(self, name, args)
    def isHCall(self):
        return True

class FRule(object):
    def __init__(self, name, params, body):
        self.name = name
        self.params = params
        self.body = body
    def __str__(self):
        params_s = ",".join(self.params)
        body_s = "%s" % self.body
        return self.name + "(" + params_s + ")=" + body_s + ";"

class GRule(object):
    def __init__(self, name, cname, cparams, params, body):
        self.name = name
        self.cname = cname
        self.cparams = cparams
        self.params = params
        self.body = body
    def __str__(self):
        params_s = ",".join(self.params)
        cparams_s = ",".join(self.cparams)
        pat_s = self.cname
        if len(self.cparams) > 0 :
            pat_s += "(" + cparams_s + ")"
        if len(self.params) > 0:
            pat_s += ","
        body_s = "%s" % self.body
        return self.name + "(" + pat_s + params_s + ")=" + body_s + ";"

class HRule(object):
    def __init__(self, name, patternList, body):
        self.name = name
        self.patternList = patternList
        self.body = body
    def __str__(self):
        patterns_s = ",".join([str(pattern) for pattern in self.patternList])
        body_s = "%s" % self.body
        return self.name + "(" + patterns_s + ")=" + body_s + ";"

class LetCall(object):
    def __init__(self, params, call):
        self.params = params
        self.call = call

class ARule(object):
    def __init__(self, name, patternList, letCallList, bodyList, outArity):
        self.name = name
        self.patternList = patternList
        self.letCallList = letCallList
        self.bodyList = bodyList
        self.outArity = outArity

class StackBottom(Exp):
    def __init__(self):
        pass

    def __str__(self):
        return "⊥"
    
    def isStackBottom(self):
        return True
    
    def vars(self):
        return []
    
import random
class OutFormat(object):
    def __init__(self, node, root, exp=StackBottom()):
        self.exp = exp
        self.root = root
        self.node = node

class Program(object):
    def __init__(self, rules):
        self.rules = rules
    def __str__(self):
        return "".join(["%s" % r for r in self.rules])
