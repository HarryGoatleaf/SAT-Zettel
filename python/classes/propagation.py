from z3 import *

# whack hack
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# now import own classes
import classes.cnf as cnf

def dpll(phi, sign):
  # check if phi is in cnf
  if not cnf.is_cnf(phi):
    raise Exception("Formula is not in CNF.")

  # get free variables in formula
  variables = [key.n for key in cnf.get_vars(phi)]
  # stack of entries (x,v,b) 
  # (x, v) encode current partial assignment
  # b is flag indicating if we tried other value for variable x
  trail = []

  def decide():
    if len(trail) >= len(variables):
      return False
    cur_var = variables[len(trail)]
    trail.append((cur_var, sign, False))
    return True

  def backtrack():
    while len(trail) > 0:
      (var, val, flag) = trail.pop()
      if not flag:
        # found unexplored subtree
        trail.append((var, not val, True))
        return True
    # explored all assignments
    return False
  
  def BCP():
    while cnf.has_unit_clause(phi, trail):
      (variable, value) = cnf.find_implication(phi, trail)
      trail.append((variable, value, True))
    if cnf.check_partial_assignment(phi, trail) == False:
      # formula has unsatisfied clause
      return False
    else:
      # formula is either sat or undetermined
      return True

  if not BCP(): return False
  while(True):
    if not decide(): return True
    while not BCP():
      if not backtrack(): return False