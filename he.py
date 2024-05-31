from sll_language import *
from algebra import *

def embeddedIn(e1, e2, asSpecialCase=False):
    return he(e1, e2)

def he(e1, e2, asSpecialCase=False):
    return heByDiving(e1, e2, asSpecialCase) or heByCoupling(e1, e2, asSpecialCase)

def heByDiving(e1, e2, asSpecialCase) :
    if e2.isVar():
        return False
    elif e2.isCall():
        return any([he(e1, e, asSpecialCase) for e in e2.args])

def heByCoupling(e1, e2, asSpecialCase):
    if e1.isVar() and (asSpecialCase or e2.isVar()):
        return True
    elif e1.hasTheSameFunctorAs(e2):
        if asSpecialCase:
            return all(map(heByCoupling, e1.args, e2.args, [asSpecialCase]*len(e1.args)))
        return all(map(he, e1.args, e2.args, [asSpecialCase]*len(e1.args)))
