/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.PresheafTensorEvaluation

/-!
# The actual finite-sum AW component square

This degreewise identity uses the real finite antidiagonal
sum. It neither assumes the square nor replaces AW by a chosen quasi-isomorphism.
The total-tensor comparison is not yet packaged as a chain map.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))

/-- Actual evaluated AW agrees degreewise with objectwise AW after the chosen
coproduct comparison. -/
theorem reducedTorusAW_evaluation_component (q n : ℕ) :
    ((reducedTorusPresheafAW k q).f n).app (op U) ≫
      (presheafTensorEvaluationXIso k U
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k 1)) n).hom =
    (reducedTorusObjectwiseAW k U q).f n := by
  simp only [reducedTorusPresheafAW, reducedTorusObjectwiseAW,
    alexanderWhitney, awApp, NatTrans.app_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro ij hij
  have h : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  simp only [awTerm, dite_eq_left h, NatTrans.comp_app, Category.assoc]
  rw [presheafTensorEvaluationXIso_ι]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
