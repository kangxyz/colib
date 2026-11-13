/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulOverBase.ComplexOverBase
public import StacksFrontier.Homology.CyclesShortComplex

/-! # The short exact coordinate sequence on the projective line

The three nonzero terms of the standard acyclic coordinate Koszul complex at twist
`-2` give the actual sequence used to compute the signed second coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjKoszulOverBase

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "C" => koszulOver 1 X (-2)

/-- The canonical two-coordinate Koszul sequence, with its actual differentials. -/
def projectiveLineEulerSequence :=
  ShortComplex.mk ((C).d 0 1) ((C).d 1 2) ((C).d_comp_d 0 1 2)

/-- The Euler sequence is exact at both endpoints as well as at the middle. -/
theorem projectiveLineEulerSequence_shortExact : (projectiveLineEulerSequence X).ShortExact := by
  let h : (C).Acyclic := acyclic_koszulOver 1 X (-2)
  have h₃ : IsZero ((C).X 3) := isZero_koszulOver_X 1 X (-2) 3 (Or.inr (by norm_num))
  have hleft := (C).cyclesShortComplex_shortExact
    (show (ComplexShape.up ℤ).Rel 0 1 from rfl) (h 1)
  have hright := (C).cyclesShortComplex_shortExact
    (show (ComplexShape.up ℤ).Rel 1 2 from rfl) (h 2)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact ((C).exactAt_iff' (i := 0) (j := 1) (k := 2)
      ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 1 2 from rfl))).mp (h 1)
  · have hz : IsZero ((C).cycles 0) := by
      have hPrev : IsZero ((C).X (-1)) := isZero_koszulOver_X 1 X (-2) (-1)
        (Or.inl (by norm_num))
      have hh := (C).cyclesShortComplex_shortExact
        (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) (h 0)
      let : Epi ((C).toCycles (-1) 0) := hh.epi_g
      exact IsZero.of_epi ((C).toCycles (-1) 0) hPrev
    have : Mono ((C).toCycles 0 1) := hleft.exact.mono_g (hz.eq_of_src _ _)
    change Mono ((C).d 0 1)
    rw [← (C).toCycles_i 0 1]
    infer_instance
  · let e := (C).iCyclesIso 2 3
      ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 2 3 from rfl))
      (h₃.eq_of_tgt _ _)
    have : Epi ((C).toCycles 1 2) := hright.epi_g
    have : Epi ((C).iCycles 2) := by
      change Epi e.hom
      infer_instance
    change Epi ((C).d 1 2)
    rw [← (C).toCycles_i 1 2]
    infer_instance

end AlgebraicGeometry.Scheme
