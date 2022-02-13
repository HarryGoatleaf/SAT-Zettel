from z3 import *
import sys
import os
import unittest

# whack hack
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# now import own classes
import classes.cnf as cnf
import classes.enumeration as enumeration

class Test(unittest.TestCase):
    def setUp(self):
      # declare vars
      # variable order inherently given by order of list
      self.x = Bools('x0 x1')
      self.psi = And()
    
    def test_enumeration(self):
      # declare formula
      phi = And(Or(self.x[0], self.x[1]), Or(Not(self.x[0])))
      self.assertTrue(enumeration.enumeration(phi, False))
      
    def test_enumeration_edge_cases(self):
      # declare formula
      # no clauses
      phi = And()
      self.assertTrue(enumeration.enumeration(phi, False))
      # empty clause
      psi = And(Or())
      self.assertFalse(enumeration.enumeration(psi, False))
      
    def test_enumeration_with_smtlibv2(self):
      phi = parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and (or x y)))')[0]
      self.assertTrue(enumeration.enumeration(phi, False))