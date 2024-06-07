from sll_language import *
from algebra import *

def moreGeneralEmbeddedIn(e1, e2, newName):
    return ge(e1, e2, newName)

def ge(e1, e2, newName):
    if geByCoupling(e1, e2):
        return (e2, Var(newName))
    else:
        return geByDiving(e1, e2, newName)

def geByDiving(e1, e2, newName) :
    if e2.isVar():
        return (None, None)
    elif e2.isCall():
        for i, e in enumerate(e2.args):
            (C, E) = ge(e1, e, newName)

            if C:
                newE = e2.cloneFunctor(e2.args)
                newE.args[i] = E
                return (C, newE)
        return (None, None)

def geByCoupling(e1, e2):
    if e1.isVar():
        return True
    elif e1.hasTheSameFunctorAs(e2):
        return all(map(geByCoupling, e1.args, e2.args))

# from sll_parser import pExp, pProg


# input1, input2 = "F(v1)", "G(v0, F(H(v2)))"
# e1 = pExp(input1)
# e2 = pExp(input2)
# (C, D) = ge(e1, e2, "a")
# print(C)
# print(D)