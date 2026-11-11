/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientPrismNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitPullbackPrism

/-!
# Original zero normalization of the genuine first coefficient tensor slice

First use the actual tensor-zero row isomorphisms. Then use precisely the existing canonical
zero normalization of the tensor functor in the second input. Conjugating the independently
constructed first-row automorphism by these displayed isomorphisms gives the original normalized
tensor transformation, followed by the original one-row embedding. The entire fixed-cell prism
therefore agrees with the original suspension-row cylinder before realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
  CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual tensor functor with exactly its original chosen-zero normalization. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientNormalization.lean:33"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def tensorUnitPullbackNormalizedFunctor :
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  CategoryTheory.rebaseFunctor (boundedAboveFlatPerfectTensorUnitPullback f)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero
    (((boundedAboveFlatPerfectTensorUnitPullback_exact f).zero
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)

/-- The two genuine coefficient-zero comparisons followed by the original input normalization. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientNormalization.lean:43"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def tensorUnitPullbackFirstRowNormalization :
    boundedAboveFlatPerfectPullback f ⋙ boundedAboveFlatPerfectTensorUnitFirstRow X ≅
      tensorUnitPullbackNormalizedFunctor f ⋙ oneEmbedding (boundedAboveFlatPerfectWaldhausen
        X.toRingedSpace) :=
  Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback f) (tensorUnitFirstRowIso X) ≪≫
    Functor.isoWhiskerRight (tensorUnitPullbackNormalization f)
    (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))

/-- Normalize the actual coefficient-row automorphism by those explicitly displayed comparisons. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientNormalization.lean:51"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def tensorUnitPullbackFirstRowNormalizedAutomorphism (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackNormalizedFunctor f ⋙ oneEmbedding (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace) ≅
      tensorUnitPullbackNormalizedFunctor f ⋙ oneEmbedding (boundedAboveFlatPerfectWaldhausen
        X.toRingedSpace) :=
  (tensorUnitPullbackFirstRowNormalization f).symm ≪≫
    Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback f)
    (tensorUnitFirstRowAutomorphism X r) ≪≫
    tensorUnitPullbackFirstRowNormalization f

set_option maxHeartbeats 800000 in
-- The native tensor comparison needs additional elaboration time; its proof is unchanged.
/-- The entire normalized first-row arrow is the original normalized tensor arrow, row by row. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientNormalization.lean:60"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
theorem tensorUnitPullbackFirstRowNormalizedAutomorphism_hom (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitPullbackFirstRowNormalizedAutomorphism f r).hom =
      whiskerRight (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
        (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) := by
  have h := tensorUnitFirstRowAutomorphism_comparison X r
  apply NatTrans.ext
  funext K
  have hK := NatTrans.congr_app h ((boundedAboveFlatPerfectPullback f).obj K)
  dsimp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at hK
  dsimp only [tensorUnitPullbackFirstRowNormalizedAutomorphism,
    tensorUnitPullbackFirstRowNormalization,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((tensorUnitFirstRowAutomorphism X r).hom.app ((boundedAboveFlatPerfectPullback f).obj K))
    ((tensorUnitFirstRowIso X).hom.app ((boundedAboveFlatPerfectPullback f).obj K))
    ((oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).map
      ((tensorUnitPullbackNormalization f).hom.app K)),
    hK]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [normalizedWeakTransformation, NatTrans.comp_app,
    Functor.map_comp]
  rfl

/-- The actual normalized coefficient arrow uncurried against the second grid, then first-row
restriction. Both original coefficient parameters remain independent. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientNormalization.lean:91"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
def tensorUnitPullbackNormalizedCoefficientPrism (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) k :=
  ((nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj
    (ComposableArrows.mk₁ (tensorUnitPullbackFirstRowNormalizedAutomorphism f r).hom)) ⋙
      reindex (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ

/-- The whole normalized fixed-cell slice equals the original tensor cylinder and suspension row.
-/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientNormalization.lean:101"
  "adaptation" "Actual coefficient tensor row, original zero normalization and parameter grid."]
theorem tensorUnitPullbackNormalizedCoefficientPrism_eq (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitPullbackNormalizedCoefficientPrism f r A τ θ =
      nerveCylinderDiagram (whiskerLeft A
        (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
          (boundedAboveFlatPerfectTensorUnitPullback_exact f)
          (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)) τ ⋙
        suspensionRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) θ := by
  unfold tensorUnitPullbackNormalizedCoefficientPrism
  rw [← nerveCylinderDiagram_whiskerLeft, tensorUnitPullbackFirstRowNormalizedAutomorphism_hom]
  rw [show whiskerLeft A (whiskerRight
      (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
      (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) =
    whiskerRight (whiskerLeft A
      (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom))
      (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) from rfl]
  rw [iteratedNerveCylinderDiagram_postcomp]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0546"] tensorUnitPullbackNormalizedCoefficientPrism_eq
attribute [colib_tag "COL-0546"] tensorUnitPullbackFirstRowNormalizedAutomorphism_hom

end AlgebraicGeometry.Scheme.Modules
