/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity

/-!
# The actual projective-line chart inversion is involutive

The native equivalence fixes constants and sends X to X⁻¹. Polynomial and
localization extensionality show that applying it twice is the identity.
No second rational-function inversion or projective-line model is introduced.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open Polynomial

variable (k : Type*) [Field k]

/-- The existing chart change squared is the identity on the original rational field. -/
theorem projectiveLineChartInversion_comp_self :
    (projectiveLineChartInversion k).toRingHom.comp
      (projectiveLineChartInversion k).toRingHom = RingHom.id (RatFunc k) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · change projectiveLineChartInversion k
      (projectiveLineChartInversion k (algebraMap k[X] (RatFunc k) (C c))) =
        algebraMap k[X] (RatFunc k) (C c)
    rw [projectiveLineChartInversion_C, projectiveLineChartInversion_C]
  · change projectiveLineChartInversion k
      (projectiveLineChartInversion k (algebraMap k[X] (RatFunc k) X)) =
        algebraMap k[X] (RatFunc k) X
    rw [projectiveLineChartInversion_X, map_inv₀, projectiveLineChartInversion_X, inv_inv]

/-- The literal native rational inversion is an involution. -/
theorem projectiveLineChartInversion_involutive :
    Function.Involutive (projectiveLineChartInversion k) :=
  fun x => RingHom.congr_fun (projectiveLineChartInversion_comp_self k) x

end AlgebraicGeometry
