/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Checks for the actual lower tail over a finite coefficient extension.
These are dimension and base-case checks, not the missing rigidity induction. -/

universe u

example (K E : Type u) [Field K] [Field E] [Algebra K E] [Module.Finite K E]
    (d : ℕ) : Algebra.trdeg K (MvPolynomial (Fin d) E) = d := by
  rw [← trdeg_add_eq K E (A := MvPolynomial (Fin d) E),
    trdeg_eq_zero, zero_add, MvPolynomial.trdeg_of_isDomain]
  simp

example (K E : Type u) [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] [Algebra.IsSeparable K E] :
    Algebra.Etale K (MvPolynomial (Fin 0) E) := by
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let : Algebra.FinitePresentation K E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale K E := {}
  let : Algebra.Etale E (MvPolynomial (Fin 0) E) :=
    Algebra.Etale.of_equiv (MvPolynomial.isEmptyAlgEquiv E (Fin 0)).symm
  exact Algebra.Etale.comp K E (MvPolynomial (Fin 0) E)
