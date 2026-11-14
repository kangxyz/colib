/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.PresheafTensorChainEvaluation
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusAWComponents

/-!
# The original presheaf AW map via the actual evaluation square

The global quasi-isomorphism is derived from the proved
component square, the actual chain comparison, and native objectwise detection.
No inverse of AW is used as a chain map. This is ordinary, not derived tensor.
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

/-- Actual target chain comparison: first evaluate total tensor, then identify
the two evaluated alternating-face-map complexes with the original objectwise ones. -/
def reducedTorusEvaluateTotalTensorIso (q : ℕ) :
    (integralPresheafEvaluationChains k U).obj
      (HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k 1))) ≅
    HomologicalComplex.tensorObj
      ((alternatingFaceMapComplex _).obj (reducedTorusEvaluatedSimplicial k U q))
      ((alternatingFaceMapComplex _).obj (reducedTorusEvaluatedSimplicial k U 1)) :=
  presheafTensorEvaluationChainIso k U _ _ ≪≫
    MonoidalCategory.tensorIso (reducedTorusEvaluateChainsIso k U q)
      (reducedTorusEvaluateChainsIso k U 1)

/-- The assembled target comparison has the already-verified coproduct component. -/
theorem reducedTorusEvaluateTotalTensorIso_hom_f (q n : ℕ) :
    (reducedTorusEvaluateTotalTensorIso k U q).hom.f n =
      (presheafTensorEvaluationXIso k U
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k 1)) n).hom := by
  have ht :
      (MonoidalCategory.tensorIso (reducedTorusEvaluateChainsIso k U q)
        (reducedTorusEvaluateChainsIso k U 1)).hom.f n = 𝟙 _ := by
    change (HomologicalComplex.mapBifunctorMap
      (reducedTorusEvaluateChainsIso k U q).hom
      (reducedTorusEvaluateChainsIso k U 1).hom
      (curriedTensor (ModuleCat.{u + 1} ℤ)) (.down ℕ)).f n = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p r h
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp [reducedTorusEvaluateChainsIso,
      alternatingFaceMapComplexCompMapHomologicalComplexIso]
    rfl
  simp only [reducedTorusEvaluateTotalTensorIso, Iso.trans_hom,
    HomologicalComplex.comp_f, presheafTensorEvaluationChainIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, ht]
  exact Category.comp_id _

/-- Assemble the verified degreewise AW square into a square of chain maps. -/
theorem reducedTorusAW_evaluation_square (q : ℕ) :
    (integralPresheafEvaluationChains k U).map (reducedTorusPresheafAW k q) ≫
        (reducedTorusEvaluateTotalTensorIso k U q).hom =
      (reducedTorusEvaluateTensorChainsIso k U q).hom ≫
        reducedTorusObjectwiseAW k U q := by
  ext n : 1
  have hs : (reducedTorusEvaluateTensorChainsIso k U q).hom.f n = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    reducedTorusEvaluateTotalTensorIso_hom_f, hs, Category.id_comp]
  exact reducedTorusAW_evaluation_component k U q n

/-- The actual evaluated presheaf AW map is a quasi-isomorphism, by its proved square. -/
instance reducedTorusEvaluatedPresheafAW_quasiIso (q : ℕ) :
    QuasiIso ((integralPresheafEvaluationChains k U).map
      (reducedTorusPresheafAW k q)) := by
  have h : QuasiIso
      ((integralPresheafEvaluationChains k U).map (reducedTorusPresheafAW k q) ≫
        (reducedTorusEvaluateTotalTensorIso k U q).hom) := by
    rw [reducedTorusAW_evaluation_square]
    infer_instance
  exact (quasiIso_iff_comp_right
    ((integralPresheafEvaluationChains k U).map (reducedTorusPresheafAW k q))
    (reducedTorusEvaluateTotalTensorIso k U q).hom).mp h

/-- Native objectwise detection yields QuasiIso for the original presheaf AW map.
No sheaf-section exactness or K-flatness is asserted. -/
instance reducedTorusPresheafAW_quasiIso (q : ℕ) :
    QuasiIso (reducedTorusPresheafAW k q) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro V
  exact reducedTorusEvaluatedPresheafAW_quasiIso k V.unop q

end AlgebraicGeometry.PresheafWithTransfers
