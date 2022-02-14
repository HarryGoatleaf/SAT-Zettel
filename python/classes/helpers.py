from z3 import *

def is_bool_var(phi):
  """ Is true iff phi is a boolean variable. """
  return is_bool(phi) and is_const(phi) and not is_bool_val(phi)

def is_bool_val(phi):
  """ Is true iff phi is a constant boolean value, i.e. either true or false. """
  return is_true(phi) or is_false(phi)
  
def is_bool_literal(phi):
  """ Is true iff phi is either a boolean variable or a negated boolean variable. """
  return is_bool_var(phi) or (is_not(phi) and is_bool_var(phi.children()[0]))