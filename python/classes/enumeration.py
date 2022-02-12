from z3 import *

# whack hack
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# now import own classes
import classes.cnf as cnf

def enumeration(phi, try_first):
  """
  Applies the SAT-solving technique 'enumaration' to the boolean formula phi

  Parameters
  ----------
  phi
    Boolean formula
  try_first
    Boolean value that we try first
    
  Returns
  -------
  True iff. phi is satisfiable.
  """
  # check if phi is in cnf
  if not cnf.is_cnf(phi):
    raise Exception("Formula is not in CNF.")
  # get free variables in formula
  variables = [key.n for key in cnf.get_vars(phi)]

  # clear trail
  # stack of entries (x,v,b) 
  # (x, v) encode current partial assignment
  # b is flag indicating if we tried other value for variable x
  trail = []
  
  def decide():
    """
    Auxilliary function. Chooses value for unassigned variable.
    Value is always try_first.
    Variable is always next in order.
    
    Return
    ------
    True
      iff. variable was successfully assigned
    False
      iff. there are no more free variables
    """
    if len(trail) >= len(variables):
      return False
    cur_var = variables[len(trail)]
    trail.append((cur_var, try_first, False))
    return True
  
  def backtrack():
    """
    Auxilliary function.
    Removes explored partial assignments and goes to first unexplored subgraph.
    Returns
    -------
    True
      iff. we find unexplored partial assignment
    False
      iff. we explored all assignments
    """
    while len(trail) > 0:
      (var, val, flag) = trail.pop()
      if not flag:
        # found unexplored subtree
        trail.append((var, not val, True))
        return True
    # explored all assignments
    return False
  
  while(True):
    if not decide():
      if cnf.check_partial_assignment(phi, trail):
        return True
      elif not backtrack():
        return False