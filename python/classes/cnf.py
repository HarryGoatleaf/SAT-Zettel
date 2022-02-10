from z3 import *

def check_partial_assignment_CNF(phi, trail):
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
  if not check_CNF(phi):
    raise Exception("Formula is not in CNF.")
  substitutions = tuple([(var, val) for (var, val, _) in trail])
  substituted = substitute(phi, substitutions)
  
  #
  formula_has_false = False   # formula has a «false clause», i.e. a clause with only false literals
  formula_has_undetermined = False # formula has a clause where no literal is true but some are unassigned
  for clause in phi.children():
    clause_has_true = False
    clause_has_unassigned = False
    for literal in clause.children():
      # TODO: boolean refactor
      if is_bool(literal):
        has_true = has_true | is_true(literal)
      elif is_var(literal) or is_not(literal):
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

def check_CNF(phi):
  """
  Helper method that checks if a formula is in CNF.
  """
  if not is_and(phi): return False
  for clause in phi.children():
    if not is_or(clause): return False
    for literal in clause.children():
      if not (is_var(literal) or (is_not(literal) and is_var(literal.children()[0]))):
        return False
