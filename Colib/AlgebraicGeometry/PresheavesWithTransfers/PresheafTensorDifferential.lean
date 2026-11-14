/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.PresheafTensorEvaluation

/-!
# Signed summand differentials under presheaf evaluation

Both epsilon signs remain the native ComplexShape
coefficients. No differential compatibility is taken as an assumption.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme HomologicalComplex
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))
variable (K L : ChainComplex
  ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) ℕ)

/-- Evaluation of integral presheaf chain complexes at the actual smooth source. -/
abbrev integralPresheafEvaluationChains :=
  (((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
    (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ))

/-- The native inclusion-or-zero is respected, including off-antidiagonal terms. -/
theorem presheafTensorEvaluation_ιOrZero (p q n : ℕ) :
    (ιMapBifunctorOrZero K L (curriedTensor _) (.down ℕ) p q n).app (op U) ≫
      (presheafTensorEvaluationXIso k U K L n).hom =
    ιMapBifunctorOrZero ((integralPresheafEvaluationChains k U).obj K)
      ((integralPresheafEvaluationChains k U).obj L)
      (curriedTensor _) (.down ℕ) p q n := by
  by_cases h : p + q = n
  · simpa only [ιMapBifunctorOrZero_eq K L (curriedTensor _) (.down ℕ) p q n h,
      ιMapBifunctorOrZero_eq ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p q n h] using
      presheafTensorEvaluationXIso_ι k U K L p q n h
  · simp only [ιMapBifunctorOrZero_eq_zero K L (curriedTensor _) (.down ℕ) p q n h,
      ιMapBifunctorOrZero_eq_zero ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p q n h,
      NatTrans.app_zero, zero_comp]

private theorem evaluation_signed_comp
    {A B C : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ}
    {D : ModuleCat.{u + 1} ℤ} (f : A ⟶ B) (g : B ⟶ C) (z : ℤ)
    (t : C.obj (op U) ⟶ D) (b : B.obj (op U) ⟶ D)
    (h : g.app (op U) ≫ t = b) :
    (z • (f ≫ g)).app (op U) ≫ t = z • (f.app (op U) ≫ b) := by
  simp only [NatTrans.app_zsmul, NatTrans.comp_app, Preadditive.zsmul_comp,
    Category.assoc, h]

/-- The original horizontal signed summand differential is preserved. -/
theorem presheafTensorEvaluation_d₁ (p q n : ℕ) :
    (mapBifunctor.d₁ K L (curriedTensor _) (.down ℕ) p q n).app (op U) ≫
      (presheafTensorEvaluationXIso k U K L n).hom =
    mapBifunctor.d₁ ((integralPresheafEvaluationChains k U).obj K)
      ((integralPresheafEvaluationChains k U).obj L)
      (curriedTensor _) (.down ℕ) p q n := by
  by_cases h : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
  · rw [mapBifunctor.d₁_eq' K L (curriedTensor _) (.down ℕ) h q n,
      mapBifunctor.d₁_eq' ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) h q n]
    exact evaluation_signed_comp k U _ _ _ _ _
      (presheafTensorEvaluation_ιOrZero k U K L ((ComplexShape.down ℕ).next p) q n)
  · simp only [mapBifunctor.d₁_eq_zero K L (curriedTensor _) (.down ℕ) p q n h,
      mapBifunctor.d₁_eq_zero ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p q n h,
      NatTrans.app_zero, zero_comp]

/-- The original vertical signed summand differential is preserved.
In particular, the native epsilon-two sign is not discarded. -/
theorem presheafTensorEvaluation_d₂ (p q n : ℕ) :
    (mapBifunctor.d₂ K L (curriedTensor _) (.down ℕ) p q n).app (op U) ≫
      (presheafTensorEvaluationXIso k U K L n).hom =
    mapBifunctor.d₂ ((integralPresheafEvaluationChains k U).obj K)
      ((integralPresheafEvaluationChains k U).obj L)
      (curriedTensor _) (.down ℕ) p q n := by
  by_cases h : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
  · rw [mapBifunctor.d₂_eq' K L (curriedTensor _) (.down ℕ) p h n,
      mapBifunctor.d₂_eq' ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p h n]
    exact evaluation_signed_comp k U _ _ _ _ _
      (presheafTensorEvaluation_ιOrZero k U K L p ((ComplexShape.down ℕ).next q) n)
  · simp only [mapBifunctor.d₂_eq_zero K L (curriedTensor _) (.down ℕ) p q n h,
      mapBifunctor.d₂_eq_zero ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p q n h,
      NatTrans.app_zero, zero_comp]

end AlgebraicGeometry.PresheafWithTransfers
