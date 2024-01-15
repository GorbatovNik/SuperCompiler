from sll_language import *
from sll_parser import pExp, pProg
from basic_process_tree_builder import *
from advanced_process_tree_builder import *
from residual_program_generator import *

pAdd = "gAdd(Z,y)=y;gAdd(S(x),y)=S(gAdd(x,y));"
pAddAcc = "gAddAcc(Z,y)=y;gAddAcc(S(x),y)=gAddAcc(x,S(y));"

def runBasicScp(prog, e):
	nameGen = NameGen("v", 100)
	tree = buildBasicProcessTree(nameGen, 100, prog, e)
	res = ResidualProgramGenerator(tree).genResidualProgram()
	return res

def test104BAddAdd():
	(resPr, resExp) = runBasicScp(pProg(pAdd), pExp("gAdd(gAdd(a,b),c)"))

	print('end')
	# gAdd(gAdd(S(Z),Z), Z) -> gAdd(S(gAdd(Z, Z)), Z) -> S(gAdd(gAdd(Z,Z), Z)) -> S(gAdd(Z, Z)) -> S(Z)
	# '''gAdd2(Z,c)=c;
	#    gAdd2(S(v101),c)=S(gAdd2(v101,c));
	#    gAdd1(Z,b,c)=gAdd2(b,c);
	#    gAdd1(S(v100),b,c)=S(gAdd1(v100,b,c));
	#    $gAdd1(a,b,c)'''

test104BAddAdd()
