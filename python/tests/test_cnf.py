from z3 import *
import sys
import os
import unittest

# whack hack
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# now import own classes
import classes.cnf as cnf

class Test(unittest.TestCase):
    def setUp(self):
      # declare vars
      # variable order inherently given by order of list
      self.x = Bools('x0 x1')
      # declare formula
      self.phi = Or(self.x[0], self.x[1])
      self.psi = And(self.phi, Or(Not(self.x[0])))

      # example using SMT-LIB v2
      #phi = parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and x y) )')[0]


    def test_create_formula(self):
      self.assertFalse(cnf.is_cnf(self.phi))
      self.assertTrue(cnf.is_cnf(self.psi))
      
    def test_get_free_variables(self):
      free_vars = cnf.get_vars(self.psi)
      x_set = set()
      x_set.add(cnf.askey(self.x[0]))
      x_set.add(cnf.askey(self.x[1]))
      self.assertEqual(x_set, free_vars)

    def test_evaluate(self):
      sat_trail = [(self.x[1], BoolVal(True), 0), (self.x[0], BoolVal(False), 1)]
      unsat_trail = [(self.x[0], BoolVal(True), 1)]
      self.assertIsNone(cnf.check_partial_assignment(self.psi, []))
      self.assertTrue(cnf.check_partial_assignment(self.psi, sat_trail))
      self.assertFalse(cnf.check_partial_assignment(self.psi, unsat_trail))