from z3 import *
import cnf

def is_bool_var(phi):
  """ Is true iff phi is a boolean variable. """
  return is_bool(phi) and is_const(phi) and not is_bool_val(phi)

def is_bool_val(phi):
  """ Is true iff phi is a constant boolean value, i.e. either true or false. """
  return is_true(phi) or is_false(phi)
  
def is_bool_literal(phi):
  """ Is true iff phi is either a boolean variable or a negated boolean variable. """
  return is_bool_var(phi) or (is_not(phi) and is_bool_var(phi.children()[0]))
  
def resolvable(phi, psi):
  """ Helper method that checks if two clauses are resolvable """
  if not (cnf.is_clause(phi) and cnf.is_clause(psi)):
    raise Exception("Cannot resolve non-clauses")
  for literal1 in phi.children:
    for literal2 in phi.children:
      if is_not(literal1) and is_bool_var(literal2):
        pass
