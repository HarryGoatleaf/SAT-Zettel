from z3 import *

# declare vars
# variable order inherently given by order of list
x = Bools('x0 x1')
# declare formula
phi = And(x[0], x[1])

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
  substitutions = tuple([(var, val) for (var, val, _) in trail])
  substituted = substitute(phi, substitutions)
  

def enumeration(phi, vars, try_first):
  """
  Applies the SAT-solving technique 'enumaration' to the boolean formula phi

  Parameters
  ----------
  phi
    Boolean formula
  vars
    List of variables. We assume that all free variables in phi are in vars. Order of vars implies order of enumeration.
  try_first
    Boolean value that we try first
    
  Returns
  -------
  True iff. phi is satisfiable.
  """
  # stack of entries (x,v,b) 
  # (x, v) encode current partial assignment
  # b is flag if we tried other value for variable x
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
    if len(trail) >= len(vars):
      return False
    cur_var = vars[len(trail)]
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
    while len(trail) >= 0:
      (var, val, flag) = trail.pop()
      if not flag:
        # found unexplored subtree
        trail.append((var, not val, True))
        return True
    # explored all assignments
    return False
  
  while(True):
    if not decide():
      pass




# example using SMT-LIB v2
#phi = parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and x y) )')[0]

# subst = substitute(phi, ((x[1],  BoolVal(True))) )
# print(subst)