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

def express_in_sll_terms()

def parse_program(program_text):
    try:
        global synProgram 
        synProgram = SynProgram()
        parsed_data = program.parseString(program_text, parseAll=True)
        return parsed_data
    except ParseException as pe:
        print("Parsing Failed:")
        print(pe.line)
        print(" " * (pe.column - 1) + "^")
        print(pe)

# Тестирование парсера
program_text = """
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
  def un:Any=>Any = {
	case S(x) => x
    case Z => Z
  }
}
"""


parsed_program = parse_program(program_text)
print(parsed_program)
