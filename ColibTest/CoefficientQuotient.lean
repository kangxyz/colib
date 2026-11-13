/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientQuotient

/-! # Regression tests for the actual cone-to-quotient bridge -/

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.finiteCoefficients

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

example (K : CochainComplex C ℤ) (n : ℕ) :
    integral K n ≫ toQuotient K n = quotientπ K n := by simp

example (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    n • 𝟙 ((quotient K n).X i) = 0 := nsmul_id_quotient_X K n i

example (K : CochainComplex C ℤ) (n : ℕ) [Mono (n • 𝟙 K)] :
    QuasiIso (toQuotient K n) := quasiIso_toQuotient K n
