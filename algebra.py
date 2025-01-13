import itertools

from sll_language import *

class Matcher(object):
    def __init__(self):
        self.subst = dict()
    def match(self, pattern, exp):
        if pattern.isVar():
            e = self.subst.get(pattern.vname, None)
            if e == None:
                self.subst[pattern.vname] = exp
            elif e != exp:
                self.subst = None
        elif (pattern.isCall() and
              pattern.hasTheSameFunctorAs(exp) and
              len(pattern.args) == len(exp.args)):
            for p, e in zip(pattern.args, exp.args):
                self.match(p, e)
                if self.subst == None:
                    return
        else:
            self.subst = None

def matchAgainst(pattern, exp):
    matcher = Matcher()
    matcher.match(pattern, exp);
    return matcher.subst

def instOf(e1, e2):
    return matchAgainst(e2, e1) != None

def equiv(e1, e2):
    return instOf(e1, e2) and instOf(e2, e1)

class NameGen(object):
    def __init__(self, prefix, seed):
        self.prefix = prefix
        self.tick = seed
    def freshName(self):
        tick = self.tick
        self.tick = tick+1
        return "%s%s" % (self.prefix, tick)
    def freshNameList(self, n):
        tick = self.tick
        self.tick = tick + n
        return ["%s%s" % (self.prefix, tick+k) for k in range(n)]
