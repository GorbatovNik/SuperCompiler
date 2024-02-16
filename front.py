from pyparsing import *

class SynCall:
	def __init__(self, name, args):
		self.name = name
		self.args = args

class SynFuncDef:
	def __init__(self, name):
		self.rules = []
		self.name = name

class SynRule:
	def __init__(self, patternList, body):
		self.patternList = patternList
		self.body = body

class SynVarOrCtr:
	def __init__(self, name):
		self.name = name
		
class SynProgram:
	def __init__(self):
		self.funcDefs = {}
		self.ctrs = {}
		
synProgram = None
ident = Word(alphas, alphanums + "_")
varOrCtr = Word(alphas, alphanums + "_")

def addCaseObject(t):
	synProgram.ctrs[t[0]] = 0

def addCaseClass(t):
	synProgram.ctrs[t[0]] = len(list(t[1]))
	
def addFuncDef(t):
	f = SynFuncDef(t[0])
	# print(t[1])
	f.rules = list(t[1])
	synProgram.funcDefs[t[0]] = f
	
def callAction(t):
	return SynCall(t[0], list(t[1]))

def ruleAction(t):
	return SynRule(list(t[0]), t[1])
	

LPAR = Suppress("(")
LCPAR = Suppress("{")
RCPAR = Suppress("}")
ANY = Suppress("Any")
RPAR = Suppress(")")
CLN = Suppress(":")
ARR = Suppress("=>")
EQ = Suppress("=")
DEF = Suppress("def")
CASE = Suppress("case")

# Обработка конструкторов
case_object = Suppress("case object") + ident
case_object.setParseAction(addCaseObject)
case_class = Suppress("case class") + ident + LPAR + Group(Optional(delimitedList(ident + CLN + ANY))) + RPAR
case_class.setParseAction(addCaseClass)
case_sign = (LPAR + delimitedList(ANY) + RPAR | ANY)
expr = Forward()
call = ident + LPAR + Group(delimitedList(expr)) + RPAR
call.setParseAction(callAction)
varOrCtr.setParseAction(lambda t: SynVarOrCtr(t[0]))
expr << (call | varOrCtr)
pattern_list = (LPAR + Group(delimitedList(expr)) + RPAR | Group(expr))
rule = CASE + pattern_list + ARR + expr
rule.setParseAction(ruleAction)
func_def = DEF + ident + CLN + case_sign + ARR + ANY + EQ + LCPAR + Group(OneOrMore(rule)) + RCPAR
func_def.setParseAction(addFuncDef)
object_main = Suppress("object Main") + LCPAR + Group(OneOrMore(func_def)) + RCPAR

program = OneOrMore(case_object | case_class | object_main)

from sll_language import *

def express_in_sll_terms(expr):
	global synProgram
	if isinstance(expr, SynVarOrCtr):
		return Ctr(expr.name, []) if expr.name in synProgram.ctrs else Var(expr.name)
	else:
		args = [express_in_sll_terms(e) for e in expr.args]
		return Ctr(expr.name, args) if expr.name in synProgram.ctrs else HCall(expr.name, args)

def semantic_analysis():
	global synProgram
	rules = []
	for func in synProgram.funcDefs.values():
		for rule in func.rules:
			patternList = [express_in_sll_terms(e) for e in rule.patternList]
			rules.append(HRule(func.name, patternList, express_in_sll_terms(rule.body)))
	return Program(rules)

def parse_program(program_text):
	try:
		global synProgram 
		synProgram = SynProgram()
		program.parseString(program_text, parseAll=True)
		sllProg = semantic_analysis()
		sllTask = HCall('main',[Var(v.name) for v in synProgram.funcDefs['main'].rules[0].patternList])
		return sllProg, sllTask
	except ParseException as pe:
		print("Parsing Failed:")
		print(pe.line)
		print(" " * (pe.column - 1) + "^")
		print(pe)

def generate_scala(resProg, resExp):
	ctrs = {}
	def ctrsTrawl(exp):
		if exp.isCtr():
			ctrs[exp.name] = len(exp.args)
		if exp.isCall():
			for arg in exp.args:
				ctrsTrawl(arg)

	for rule in resProg.rules:
		for patt in rule.patternList:
			ctrsTrawl(patt)
		ctrsTrawl(rule.body)
	ctrsTrawl(resExp)

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
	for rule in resProg.rules:
		if rule.name not in funcs:
			funcs[rule.name] = []
		funcs[rule.name].append(rule)

	def getAnySign(size):
		return "Any" if size == 1 else "(Any" + ", Any"*(size - 1) + ")"

	def getLeftSide(patternList):
		if len(patternList)==1:
			l = str(patternList[0])
		else:
			l = "(" + str(patternList[0])
			for i in range(len(patternList)-1):
				l += ", " + str(patternList[i+1])
			l += ")"
		return l
	
	main_vars = resExp.vars()
	scala+="object Main {\n\tdef main : " + getAnySign(len(main_vars)) + " => Any = {\n\t\tcase " + getLeftSide(main_vars) + " => " + str(resExp) + "\n\t}\n"
	
	for func_name, rules in funcs.items():
		scala+="\tdef " + func_name + " : " + getAnySign(len(rules[0].patternList)) + " => Any = {\n"
		for rule in rules:
			scala+="\t\tcase " + getLeftSide(rule.patternList) + " => " + str(rule.body) + "\n"
		scala+="\t}\n"
	scala+="}\n"
	return scala


# Тестирование парсера
program_text1 = """
case object Z
case object False
case object True

case class S(x: Any)

object Main {
  def main : (Any, Any) => Any = {
    case (a, b) => eq(S(a),b)
  }
  def eq : (Any, Any) => Any = {
    case (S(x), S(y)) => eq(x, y)
    case (S(x), Z) => False
    case (Z, S(y)) => False
    case (Z, Z) => True
  }
}
"""
program_text2 = """
case object A
case object B
case object C
case object Nil_
case class Cons(head: Any, tail: Any)
 
object Main {
  def fab : Any => Any = {
    case Cons(A, xs) => Cons(B, fab(xs))
    case Cons(x, xs) => Cons(x, fab(xs))
    case Nil_ => Nil_
  }
 
  def fbc : Any => Any = {
    case Cons(B, xs) => Cons(C, fbc(xs))
    case Cons(x, xs) => Cons(x, fbc(xs))
    case Nil_ => Nil_
  }
 
  def main : Any => Any = {
    case xs => fbc(fab(xs))
  }
}
"""
from basic_process_tree_builder import *
from advanced_process_tree_builder import *
from residual_program_generator import *

sll_prog, sll_task = parse_program(program_text2)
nameGen = NameGen("v", 100)
tree = buildAdvancedProcessTree(nameGen, 100, sll_prog, sll_task)
(resPr, resExp) = ResidualProgramGenerator(tree).genResidualProgram()
print(tree)
print(resPr)
print(resExp)
print(generate_scala(resPr, resExp))
# print(str(parsed_program))
