from z3 import *

# declare vars
# variable order inherently given by order of list
x = Bools('x0 x1')
# declare formula
phi = And(x[0], x[1])

# example using SMT-LIB v2
#phi = parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and x y) )')[0]

# subst = substitute(phi, ((x[1],  BoolVal(True))) )
# print(subst)

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
  # get free variables in formula
  vars = list(get_vars(phi))

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

def get_vars(f):
    r = set()
    def collect(f):
      if is_const(f): 
          if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
              r.add(askey(f))
      else:
          for c in f.children():
              collect(c)
    collect(f)
    return r

