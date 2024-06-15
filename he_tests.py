import unittest

from sll_language import *
from sll_parser import pExp, pProg
from he import embeddedIn, he

class HE_Tests(unittest.TestCase):

    def heTrue(self, input1, input2):
        e1 = pExp(input1)
        e2 = pExp(input2)
        self.assertTrue(he(e1, e2))

    def heFalse(self, input1, input2):
        e1 = pExp(input1)
        e2 = pExp(input2)
        self.assertFalse(he(e1, e2))

    def testVV(self):
        "v1 <| v2"
        self.heTrue("v1", "v2")

    def testVF(self):
        "v1 <| F(v2)"
        self.heTrue("v1", "F(v2)")

    def testFV(self):
        "not F(v2) <| v1"
        self.heFalse("F(v2)", "v1")

    def testDiving(self):
        "F(v1) < G(v0, F(G(v2)))"
        self.heTrue("F(v1)", "G(v0, F(H(v2)))")
    
    def testDiving2(self):
        "F(v1) < G(v0, F(G(Z)))"
        self.heFalse("F(v1)", "G(v0, F(H(Z)))")

    def testCoupling1(self):
        "F(v1, G(v2)) <| F(H(w1), G(w2))"
        self.heTrue("F(v1, G(v2))", "F(H(w1), G(w2))")

    def testCoupling2(self):
        "not f(v1) <| g(w1)"
        self.heFalse("f(v1)", "g(w1)")

    def testSpecCase1(self):
        "not f(x) <| f(Z)"
        "f(x) -> f(Z)"
        self.heFalse("f(x)", "f(Z)")

    def testSpecCase2(self):
        "not S(Z) <| T(S(Z))"
        "f(x) -> f(Z)"
        self.heFalse("f(x)", "f(Z)")