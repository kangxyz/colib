/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientNormalization
public import Colib.CategoryTheory.Waldhausen.AsSmall.Double
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationCylinder

/-! # Original supported tensor map and normalized coefficient edge

The actual exact functor is based by its original chosen-zero rebase. This owner currently
contains the original map, transformation and weak-equivalence proof; the three subsequent
small-cylinder declarations require their genuine separate cylinder predecessor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)

/-- The original canonically based model map underlying the unchanged exact tensor spectrum map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSmallMo\
    del.lean:33"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairModelMap :
    asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen T.hom) ⟶
      asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom) :=
  asSmallCategoryMap _ _ (tensorSupportedPair_exact p).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The actual coefficient crossing with precisely the existing small-model and zero transports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSmallMo\
    del.lean:40"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedPairModelTransformation
    (r : (Γ(S.right, ⊤))ˣ) :
    (tensorSupportedPairModelMap p).hom.toFunctor ⟶ (tensorSupportedPairModelMap p).hom.toFunctor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation (tensorSupportedPair_exact p)
      (tensorSupportedPair_exact p)
      (tensorSupportedPairAutomorphism p r).hom) AsSmall.up)

/-- Weak equivalences of the original tensor edge survive the specified canonical transports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSmallMo\
    del.lean:49"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorSupportedPairModelTransformation_weak
    (r : (Γ(S.right, ⊤))ˣ)
    (A : (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen T.hom)).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).obj.waldhausen.weq
      ((tensorSupportedPairModelTransformation p r).app A) :=
  normalizedWeakTransformation_weak (tensorSupportedPair_exact p)
    (tensorSupportedPair_exact p)
    (tensorSupportedPairAutomorphism p r).hom
    (fun _ ↦ (boundedAboveFlatPerfectSupportedWaldhausen S.hom).weq_iso _ inferInstance)
    (AsSmall.down.obj A)


end AlgebraicGeometry.Scheme.Modules
