/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientAutomorphism
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedPairNaturality

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
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)

/-- The actual tensor functor with exactly its original chosen-zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:33"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairNormalizedFunctor :
    (boundedAboveFlatPerfectSupported T.hom).FullSubcategory ⥤
      (boundedAboveFlatPerfectSupported S.hom).FullSubcategory :=
  CategoryTheory.rebaseFunctor (tensorSupportedPairFunctor p)
    (boundedAboveFlatPerfectSupportedWaldhausen T.hom).zero
    (boundedAboveFlatPerfectSupportedWaldhausen S.hom).zero
    (((tensorSupportedPair_exact p).zero
      (boundedAboveFlatPerfectSupportedWaldhausen T.hom).isZero).iso
      (boundedAboveFlatPerfectSupportedWaldhausen S.hom).isZero)

/-- The actual supported functor retains its original chosen-zero normalization iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:44"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairNormalization :=
  CategoryTheory.rebaseFunctorIso (tensorSupportedPairFunctor p)
    (boundedAboveFlatPerfectSupportedWaldhausen T.hom).zero
    (boundedAboveFlatPerfectSupportedWaldhausen S.hom).zero
    (((tensorSupportedPair_exact p).zero
      (boundedAboveFlatPerfectSupportedWaldhausen T.hom).isZero).iso
      (boundedAboveFlatPerfectSupportedWaldhausen S.hom).isZero)

/-- The two genuine coefficient-zero comparisons followed by the original input normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:53"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairFirstRowNormalization :
    boundedAboveFlatPerfectSupportedPullback p ⋙
      boundedAboveFlatPerfectSupportedTensorUnitFirstRow S.hom ≅
      tensorSupportedPairNormalizedFunctor p ⋙
      oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom) :=
  Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupportedPullback p)
    (supportedTensorUnitFirstRowIso S.hom) ≪≫
    Functor.isoWhiskerRight (tensorSupportedPairNormalization p)
    (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom))

/-- Normalize the actual coefficient-row automorphism by those explicitly displayed comparisons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:64"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairFirstRowNormalizedAutomorphism (r : (Γ(S.right, ⊤))ˣ) :
    tensorSupportedPairNormalizedFunctor p ⋙
      oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom) ≅
      tensorSupportedPairNormalizedFunctor p ⋙
      oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom) :=
  (tensorSupportedPairFirstRowNormalization p).symm ≪≫
    Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupportedPullback p)
    (supportedTensorUnitFirstRowAutomorphism S.hom r) ≪≫
    tensorSupportedPairFirstRowNormalization p

set_option maxHeartbeats 800000 in
-- The unchanged original conjugation proof needs more elaboration steps on native tensor data.
/-- The entire normalized first-row arrow is the original normalized tensor arrow, row by row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:75"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorSupportedPairFirstRowNormalizedAutomorphism_hom (r : (Γ(S.right, ⊤))ˣ) :
    (tensorSupportedPairFirstRowNormalizedAutomorphism p r).hom =
      whiskerRight (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom)
        (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom)) := by
  have h := supportedTensorUnitFirstRowAutomorphism_comparison S.hom r
  apply NatTrans.ext
  funext K
  have hK := NatTrans.congr_app h ((boundedAboveFlatPerfectSupportedPullback p).obj K)
  dsimp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at hK
  dsimp only [tensorSupportedPairFirstRowNormalizedAutomorphism,
    tensorSupportedPairFirstRowNormalization,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((supportedTensorUnitFirstRowAutomorphism S.hom r).hom.app
      ((boundedAboveFlatPerfectSupportedPullback p).obj K))
    ((supportedTensorUnitFirstRowIso S.hom).hom.app
      ((boundedAboveFlatPerfectSupportedPullback p).obj K))
    ((oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).map
      ((tensorSupportedPairNormalization p).hom.app K)),
    hK]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [normalizedWeakTransformation, NatTrans.comp_app,
    Functor.map_comp]
  rfl

/-- The actual normalized coefficient arrow uncurried against the second grid, then first-row
restriction. Both original coefficient parameters remain independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:108"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairNormalizedCoefficientPrism (r : (Γ(S.right, ⊤))ˣ)
    {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectSupported T.hom).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedAboveFlatPerfectSupportedWaldhausen S.hom) k :=
  ((nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj
    (ComposableArrows.mk₁ (tensorSupportedPairFirstRowNormalizedAutomorphism p r).hom)) ⋙
      reindex (boundedAboveFlatPerfectSupportedWaldhausen S.hom) θ

/-- The whole normalized fixed-cell slice equals the original tensor cylinder and suspension row.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientNormali\
    zation.lean:119"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorSupportedPairNormalizedCoefficientPrism_eq (r : (Γ(S.right, ⊤))ˣ)
    {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedAboveFlatPerfectSupported T.hom).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorSupportedPairNormalizedCoefficientPrism p r A τ θ =
      nerveCylinderDiagram (whiskerLeft A
        (normalizedWeakTransformation (tensorSupportedPair_exact p)
          (tensorSupportedPair_exact p)
          (tensorSupportedPairAutomorphism p r).hom)) τ ⋙
        suspensionRow (boundedAboveFlatPerfectSupportedWaldhausen S.hom) θ := by
  unfold tensorSupportedPairNormalizedCoefficientPrism
  rw [← nerveCylinderDiagram_whiskerLeft, tensorSupportedPairFirstRowNormalizedAutomorphism_hom]
  rw [show whiskerLeft A (whiskerRight
      (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom)
      (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom))) =
    whiskerRight (whiskerLeft A
      (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom))
      (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom)) from rfl]
  rw [iteratedNerveCylinderDiagram_postcomp]
  rfl

end AlgebraicGeometry.Scheme.Modules
