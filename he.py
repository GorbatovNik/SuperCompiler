from sll_language import *
from algebra import *

def embeddedIn(e1, e2):
    return he(e1, e2)

def he(e1, e2):
    return heByDiving(e1, e2) or heByCoupling(e1, e2)

def heByDiving(e1, e2) :
    if e2.isVar():
        return False
    elif e2.isCall():
        return any([he(e1, e) for e in e2.args])

def heByCoupling(e1, e2):
    if e1.isVar() and e2.isVar():
        return True
    elif e1.hasTheSameFunctorAs(e2):
        return all(map(he, e1.args, e2.args))
