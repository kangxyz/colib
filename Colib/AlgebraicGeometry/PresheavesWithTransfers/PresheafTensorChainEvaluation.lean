/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.PresheafTensorDifferential

/-!
# The full signed tensor evaluation chain comparison

The differential square is proved from the actual
preserved coproduct and the verified two signed summand identities.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme HomologicalComplex
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))
variable (K L : ChainComplex
  ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) ℕ)

/-- Evaluation commutes with the full signed differential of the original total. -/
theorem presheafTensorEvaluation_d (n m : ℕ) :
    ((HomologicalComplex.tensorObj K L).d n m).app (op U) ≫
        (presheafTensorEvaluationXIso k U K L m).hom =
      (presheafTensorEvaluationXIso k U K L n).hom ≫
        (HomologicalComplex.tensorObj ((integralPresheafEvaluationChains k U).obj K)
          ((integralPresheafEvaluationChains k U).obj L)).d n m := by
  apply Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit
      ((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U))
      (presheafTensorAntidiagonal k K L n))
  rintro ⟨⟨p, q⟩, h⟩
  change (ιTensorObj K L p q n h).app (op U) ≫ _ =
    (ιTensorObj K L p q n h).app (op U) ≫ _
  have hs :
      ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorObj K L).d n m =
        mapBifunctor.d₁ K L (curriedTensor _) (.down ℕ) p q m +
          mapBifunctor.d₂ K L (curriedTensor _) (.down ℕ) p q m := by
    rw [mapBifunctor.d_eq, Preadditive.comp_add,
      mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  have ht :
      ιTensorObj ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) p q n h ≫
        (HomologicalComplex.tensorObj ((integralPresheafEvaluationChains k U).obj K)
          ((integralPresheafEvaluationChains k U).obj L)).d n m =
        mapBifunctor.d₁ ((integralPresheafEvaluationChains k U).obj K)
          ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p q m +
        mapBifunctor.d₂ ((integralPresheafEvaluationChains k U).obj K)
          ((integralPresheafEvaluationChains k U).obj L) (curriedTensor _) (.down ℕ) p q m := by
    rw [mapBifunctor.d_eq, Preadditive.comp_add,
      mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  calc
    _ = ((ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorObj K L).d n m).app (op U)) ≫
        (presheafTensorEvaluationXIso k U K L m).hom := by
          simp only [NatTrans.comp_app, Category.assoc]
    _ = _ := by
      rw [hs, NatTrans.app_add, Preadditive.add_comp,
        presheafTensorEvaluation_d₁, presheafTensorEvaluation_d₂, ← ht]
      rw [← Category.assoc, presheafTensorEvaluationXIso_ι]


/-- The native evaluation/total-tensor chain isomorphism, with the signed square proved. -/
def presheafTensorEvaluationChainIso :
    (integralPresheafEvaluationChains k U).obj (HomologicalComplex.tensorObj K L) ≅
      HomologicalComplex.tensorObj ((integralPresheafEvaluationChains k U).obj K)
        ((integralPresheafEvaluationChains k U).obj L) :=
  HomologicalComplex.Hom.isoOfComponents
    (presheafTensorEvaluationXIso k U K L)
    (fun n m _ => (presheafTensorEvaluation_d k U K L n m).symm)

end AlgebraicGeometry.PresheafWithTransfers
