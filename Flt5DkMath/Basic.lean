/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- ============================================================================

import Flt5DkMath.FLT5StandAlone

theorem PNat.pow_add_pow_ne_pow_five
    (x y z : ℕ+) :
    x^5 + y^5 ≠ z^5 :=
  by
    intro h
    have h_eq : (x : ℕ)^5 + (y : ℕ)^5 = (z : ℕ)^5 := by
      exact Subtype.ext_iff.mp h
    exact DkMath.FLT.Five.fermatFive_no_positive_solution
      x.1 y.1 z.1 x.property y.property z.property h_eq

-- ----------------------------------------------------------------------------

#print axioms PNat.pow_add_pow_ne_pow_five
#print axioms DkMath.FLT.Five.fermatFive_no_positive_solution

-- ============================================================================

#print PNat.pow_add_pow_ne_pow_five
#print DkMath.FLT.Five.fermatFive_no_positive_solution
#print DkMath.FLT.Five.Fermat5Equation

def hello := "Thanks! for Dk.Math Magic World!"
#eval hello

/-!
# Fermat's Last Theorem at exponent five

The proof route is: normalize a positive solution to a primitive packet; choose
one of the two signed gap orientations; split the associated golden-order
factor into a unit and a fifth power; eliminate four nonzero unit classes; and
exclude the zero class by a certified strict infinite descent. Conditional
receiver theorems expose the unit-class and zero-sector boundaries, while
`flt5Target` and `fermatFive_no_positive_solution` are unconditional endpoints.

The scope is exactly positive natural numbers and exponent five. This module
does not assert the general Fermat theorem, a novel historical proof, external
peer review, or acceptance of the development beyond Lean's kernel checks.
-/
