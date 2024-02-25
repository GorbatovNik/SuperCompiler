from sll_language import *
from algebra import *

# Enhanced homeomorphic embedding:
# expressions are compared only if they belong
# to the same category (as defined by `aVarIsUnderAttack`).

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

# We distinguish a specific category of expressions:
# the ones that generate contractions in the process tree.

def aVarIsUnderAttack(e):
    if e.isGCall():
        return aVarIsUnderAttack(e.args[0])
    elif e.isVar():
        return True
    else:
        return False
