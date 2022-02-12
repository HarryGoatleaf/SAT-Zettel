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
    if not is_or(clause): return False
    for literal in clause.children():
      if is_not(literal): literal = literal.children()[0]
      if not (is_bool_val(literal) or is_bool_var(literal)): return False
  return True

def get_vars(phi):
  """
  Helper method that returns all free variables of a formula in CNF.
  """
  r = set()
  if not is_cnf(phi):
    raise Exception("Formula not in CNF")
  for clause in phi.children():
    for literal in clause.children():
      if is_not(literal): literal = literal.children()[0]
      if not askey(literal) in r and is_bool_var(literal):
        r.add(askey(literal))
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
  
  #
  formula_has_false = False   # formula has a «false clause», i.e. a clause with only false literals
  formula_has_undetermined = False # formula has a clause where no literal is true but some are unassigned
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
