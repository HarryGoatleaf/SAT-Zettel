from z3 import *

# whack hack
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# now import own classes
from classes.helpers import *

# get_vars
# copy paste from 
# https://stackoverflow.com/questions/14080398/z3py-how-to-get-the-list-of-variables-from-a-formula

## Wrapper for allowing Z3 ASTs to be stored into Python Hashtables. 
class AstRefKey:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n.hash()
    def __eq__(self, other):
        return self.n.eq(other.n)
    def __repr__(self):
        return str(self.n)

def askey(n):
    assert isinstance(n, AstRef)
    return AstRefKey(n)

def is_cnf(phi):
  """
  Helper method that checks if a formula is in CNF.
  """
  if not is_and(phi): return False
  for clause in phi.children():
    if not is_clause(clause): return False
  return True

def is_clause(phi):
  """
  Helper method that checks if a formula is a disjunction of literals.
  """
  if not is_or(phi): return False
  for literal in phi.children():
    if is_not(literal): literal = literal.children()[0]
    if not (is_bool_val(literal) or is_bool_var(literal)): return False
  return True

def is_literal(phi):
  """
  Helper method that checks if  a formula is a literal, i.e. a [negated] boolean value or variable.
  """
  if is_not(phi): phi = phi.children()[0]
  if not (is_bool_val(phi) or is_bool_var(phi)): 
    return False

def get_vars(phi):
  """
  Helper method that returns all free variables of a formula in CNF.
  """
  r = set()
  def collect(psi):
    if is_bool_var(psi) and not askey(psi) in r:
      r.add(askey(psi))
    else:
      for c in psi.children():
        collect(c)
  collect(phi)
  return r

def check_partial_assignment(phi, trail):
  """
  Helper method to check if a partial assignment (encoded by trail)
  satisfies a formula.
  Returns
  -------
  True:
    if phi is true with partial assignment
  False:
    if phi is false with partial assignment
  None:
    if phi is neither true nor false with partial assignments
  """
  if not is_cnf(phi):
    raise Exception("Formula is not in CNF.")
  substitutions = [(var, BoolVal(val)) for (var, val, _) in trail]
  substituted = phi
  for subst in substitutions:
    substituted = substitute(substituted, subst)

  # formula has a «false clause», i.e. a clause with only false literals
  formula_has_false = False
  # formula has a clause where no literal is true but some are unassigned
  formula_has_undetermined = False
  for clause in substituted.children():
    clause_has_true = False
    clause_has_unassigned = False
    for literal in clause.children():
      # TODO: boolean refactor
      if is_true(literal) or (is_not(literal) and is_false(literal.children()[0])):
        clause_has_true = True
      elif is_bool_var(literal) or (is_not(literal) and is_bool_var(literal.children()[0])):
        clause_has_unassigned = True
    if (not clause_has_true) and (not clause_has_unassigned):
      formula_has_false = True
    elif (not clause_has_true) and clause_has_unassigned:
      formula_has_undetermined = True

  if formula_has_false:
    return False
  elif formula_has_undetermined:
    return None
  else:
    return True

def is_unit(phi):
  """ Helper method that checks if a clause is unit. Assumes that assignment is already substituted. """
  if not is_clause(phi):
    raise Exception("Not a clause.")
  if len(get_vars(phi)) != 1:
    # clause has more than one unassigned literal
    return False
  if check_partial_assignment(And(phi), []) != None:
    # clause is already true
    return False
  # now we only need to check if the variable occurs positively and negatively
  appears_positive = False
  appears_negative = False
  for literal in phi.children():
    if is_bool_var(literal):
      appears_positive = True
    if is_not(literal) and is_bool_var(literal.children()[0]):
      appears_negative = True
  return (appears_positive != appears_negative)

def extract_implication(phi):
  """Helper method that extracts the variable and its implied value from a unit clause."""
  if not is_unit(phi):
    raise Exception("Can't extract from non-unit clause.")
  for literal in phi.children():
    if is_bool_var(literal):
      return (literal, True)
    elif is_not(literal) and (is_bool_var(literal.children()[0])):
      return (literal.children()[0], False)

def has_unit_clause(phi, trail=[]):
  if not is_cnf(phi):
    raise Exception("Formula is not in CNF.")
  substitutions = [(var, BoolVal(val)) for (var, val, _) in trail]
  substituted = phi
  for subst in substitutions:
    substituted = substitute(substituted, subst)
  return any(map(is_unit, substituted.children()))

def find_implication(phi, trail=[]):
  """ Helper method that extracts an implication from a unit clause in a formula in CNF"""
  if not is_cnf(phi):
    raise Exception("Formula is not in CNF.")
  substitutions = [(var, BoolVal(val)) for (var, val, _) in trail]
  substituted = phi
  for subst in substitutions:
    substituted = substitute(substituted, subst)
  # find all unit clauses
  unit_clauses = filter(is_unit, substituted.children())
  for clause in unit_clauses:
    return extract_implication(clause)
  return None
