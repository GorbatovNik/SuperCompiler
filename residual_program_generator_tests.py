# -*- coding: utf-8 -*-
'''
Created on Aug 22, 2009

@author: Sergei Romanenko
'''

import unittest

from sll_language import *
from sll_parser import pExp, pProg
from basic_process_tree_builder import *
from advanced_process_tree_builder import *
from residual_program_generator import *

class ResidualProgramGenerator_Tests(unittest.TestCase):

    # Sample programs
    pAdd = "hAdd(Z,y)=y;hAdd(S(x),y)=S(hAdd(x,y));"
    gAdd = "gAdd(Z,y)=y;gAdd(S(x),y)=S(gAdd(x,y));"

    pAddAcc = "hAddAcc(Z,y)=y;hAddAcc(S(x),y)=hAddAcc(x,S(y));"
    pEq = "hEq(S(x),S(y))=hEq(x,y);hEq(Z,Z)=True;hEq(S(x),Z)=False;hEq(Z,S(y))=False;"

#---- Basic supercompiler

    def runBasicScp(self, prog, e):
        nameGen = NameGen("v", 100)
        tree = buildBasicProcessTree(nameGen, 100, prog, e)
        res = ResidualProgramGenerator(tree).genResidualProgram()
        return res

    def basicScpOK(self, prog, e, expected):
        (resPr, resExp) = self.runBasicScp(pProg(prog), pExp(e))
        res_s = "%s$%s" % (resPr, resExp)
        self.assertEqual(expected, res_s)

    def test101BVar(self):
        "BVar"
        self.basicScpOK("", "a", "$a")
        
    def test102BCtr(self):
        "BCtr"
        self.basicScpOK("", "C(a,b)", "$C(a,b)")

    def test103BAddAB(self):
        "BAddAB"
        self.basicScpOK(
                self.pAdd,
                "hAdd(a, b)",
                "hAdd1(Z,b)=b;hAdd1(S(v100),b)=S(hAdd1(v100,b));$hAdd1(a,b)")

    def test104BAddAdd(self):
        "BAddAdd"
        self.basicScpOK(
                self.pAdd,
                # hAdd(hAdd(S(Z),Z), Z) -> hAdd(S(hAdd(Z, Z)), Z) -> S(hAdd(hAdd(Z,Z), Z)) -> S(hAdd(Z, Z)) -> S(Z)
                # '''hAdd2(Z,c)=c;
                #    hAdd2(S(v101),c)=S(hAdd2(v101,c));
                #    hAdd1(Z,b,c)=hAdd2(b,c);
                #    hAdd1(S(v100),b,c)=S(hAdd1(v100,b,c));
                #    $hAdd1(a,b,c)'''
                "hAdd(hAdd(a,b),c)",
                "hAdd2(Z,c)=c;hAdd2(S(v101),c)=S(hAdd2(v101,c));hAdd1(Z,b,c)=hAdd2(b,c);hAdd1(S(v100),b,c)=S(hAdd1(v100,b,c));$hAdd1(a,b,c)")

    def test105BAddAccAB(self):
        "BAddAccAB"
        self.basicScpOK(
                self.pAddAcc,
                "hAddAcc(a, b)",
                "hAddAcc1(Z,b)=b;hAddAcc1(S(v100),b)=hAddAcc1(v100,S(b));$hAddAcc1(a,b)")

#---- Advanced supercompiler

    def runAdvancedScp(self, prog, e):
        nameGen = NameGen("v", 100)
        tree = buildAdvancedProcessTree(nameGen, 100, prog, e)
        res = ResidualProgramGenerator(tree).genResidualProgram()
        return res

    def advancedScpOK(self, prog, e, expected):
        (resPr, resExp) = self.runAdvancedScp(pProg(prog), pExp(e))
        res_s = "%s$%s" % (resPr, resExp)
        self.assertEqual(expected, res_s)

    def test201AdvAddAB(self):
        "AdvAddAB"
        self.advancedScpOK(
           self.pAdd,
           "hAdd(a,b)",
           "hAdd1(Z,b)=b;hAdd1(S(v100),b)=S(hAdd1(v100,b));$hAdd1(a,b)")

    def test202AdvAddAA(self):
        "AdvAddAA"
        self.advancedScpOK(
           self.pAdd,
           "hAdd(a, a)",
           "hAdd1(Z,v103)=v103;hAdd1(S(v104),v103)=S(hAdd1(v104,v103));$hAdd1(a,a)")

    def test203AdvAddAdd(self):
        "AdvAddAdd"
        self.advancedScpOK(
           self.pAdd,
           "hAdd(hAdd(a,b),c)",
           "hAdd2(Z,c)=c;hAdd2(S(v101),c)=S(hAdd2(v101,c));hAdd1(Z,b,c)=hAdd2(b,c);hAdd1(S(v100),b,c)=S(hAdd1(v100,b,c));$hAdd1(a,b,c)")

    def test204AdvAddAccAB(self):
        "AdvAddAccAB"
        self.advancedScpOK(
           self.pAddAcc,
           "hAddAcc(a, b)",
           "hAddAcc1(Z,b)=b;hAddAcc1(S(v100),b)=hAddAcc1(v100,S(b));$hAddAcc1(a,b)")

    def test205AdvAddAccAA(self):
        "AdvAddAccAB"
        self.advancedScpOK(
           self.pAddAcc,
           "hAddAcc(a, a)",
           "hAddAcc1(Z,v103)=v103;hAddAcc1(S(v104),v103)=hAddAcc1(v104,S(v103));$hAddAcc1(a,a)")

    def test206AdvAddAccAddAcc(self):
        "AdvAddAccAddAcc"
        self.advancedScpOK(
           self.pAddAcc,
           "hAddAcc(hAddAcc(a,b),c)",
           "hAddAcc2(Z,c)=c;hAddAcc2(S(v101),c)=hAddAcc2(v101,S(c));hAddAcc1(Z,b,c)=hAddAcc2(b,c);hAddAcc1(S(v100),b,c)=hAddAcc1(v100,S(b),c);$hAddAcc1(a,b,c)")
