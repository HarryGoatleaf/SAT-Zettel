from z3 import *
import sys
import os
import unittest

# whack hack
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
# now import own classes
import classes.cnf as cnf
import classes.propagation as propagation

class Test(unittest.TestCase):
    def setUp(self):
      # declare vars
      # variable order inherently given by order of list
      self.x = Bools('x0 x1')
      # clause with one element
      self.phi1 = Or(self.x[0])
      self.phi2 = Or(BoolVal(True), self.x[0])
      self.phi3 = Or(BoolVal(False), Not(self.x[0]))
      self.phi4 = Or(Not(BoolVal(True)), self.x[0])
      self.phi5 = Or( self.x[0],Not(self.x[0]) )
      
      # formulas
      self.psi1 = And(self.phi1)
      self.psi2 = And(self.phi3)
      self.psi3 = And(self.phi4)

      # some test formulas
      self.phi_sat = []
      self.phi_unsat = []
      self.phi_sat.append(parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and (or x y)))')[0])
      self.phi_sat.append(parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and (or (not x) y) (or x) ))')[0])
      self.phi_unsat.append(parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and (or (not x) y) (or x) (or (not y))))')[0])
      self.phi_sat.append(parse_smt2_string('(declare-const y Bool) (declare-const x Bool) (assert (and (or x y) (or (not x) (not y)) (or (not x) y)))')[0])
      self.phi_unsat.append(parse_smt2_string('(declare-const y Bool) (declare-const x Bool) \
        (assert (and (or x y) (or (not x) (not y)) (or (not x) y) (or x (not y)) ))')[0])

    def test_unit(self):
      # clause with one element
      self.assertTrue(cnf.is_unit(self.phi1))
      self.assertFalse(cnf.is_unit(self.phi2))
      self.assertTrue(cnf.is_unit(self.phi3))
      self.assertTrue(cnf.is_unit(self.phi4))
      self.assertFalse(cnf.is_unit(self.phi5))
      
    def test_extract_implication_form_unit_clause(self):
      self.assertEqual(cnf.extract_implication(self.phi1), (self.x[0], True))
      self.assertEqual(cnf.extract_implication(self.phi3), (self.x[0], False))
      self.assertEqual(cnf.extract_implication(self.phi4), (self.x[0], True))
      
    #def test_find_implication(self):
      self.assertEqual(cnf.find_implication(self.psi1), (self.x[0], True))
      self.assertEqual(cnf.find_implication(self.psi2), (self.x[0], False))
      self.assertEqual(cnf.find_implication(self.psi3), (self.x[0], True))

    def test_dpll(self):
      for phi in self.phi_sat:
        self.assertTrue(propagation.dpll(phi, False))
      for phi in self.phi_unsat:
        self.assertFalse(propagation.dpll(phi, False))