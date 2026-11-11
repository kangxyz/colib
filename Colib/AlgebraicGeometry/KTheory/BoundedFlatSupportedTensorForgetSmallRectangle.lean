/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorForgetNormalizedRectangle
public import Colib.CategoryTheory.Waldhausen.AsSmall.RouteRectangle

/-! # The original tensor/forgetting rectangle in the common universe

The independently normalized supported tensor/forgetting rectangle is lifted through the
original common-universe functors, retaining each chosen-zero normalization on both routes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSupportedSection
open GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- Original supported tensor evaluation after common-universe transport. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetSmallRectangle.l\
    ean:30"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def forgetSupportedTensorSmallIso :
    (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙ evaluationSmall (X := op
      A.right) A.hom ≅
      evaluationSmall (X := op B.right) B.hom ⋙ (tensorSupportedPairModelMap
      p).hom.toFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (forgetSupportedTensorNormalizedIso p) AsSmall.up

/-- Original ambient tensor evaluation after the same common-universe transport. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetSmallRectangle.l\
    ean:37"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def forgetAmbientTensorSmallIso :
    (boundedAboveFlatGlobalSectionModelFunctor.map p.right.op).hom.toFunctor ⋙
      GlobalSectionChangeIndex.evaluationSmall
        (op A.right) ≅
      GlobalSectionChangeIndex.evaluationSmall (op B.right) ⋙
        (tensorUnitPullbackModelMap p.right).hom.toFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (forgetAmbientTensorNormalizedIso p) AsSmall.up

set_option maxHeartbeats 800000 in
-- The unchanged full rectangle needs more elaboration steps on native geometric zero rebases.
/-- Independent common-universe lifting of the complete raw normalized forgetting square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetSmallRectangle.l\
    ean:46"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetModelIso :
    (tensorSupportedPairModelMap p ≫ tensorCoefficientSupportedForgetModel
      A.hom).hom.toFunctor ≅
      (tensorCoefficientSupportedForgetModel B.hom ≫
        tensorUnitPullbackModelMap p.right).hom.toFunctor :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down (tensorForgetNormalizedIso p)) AsSmall.up

/-- The actual supported-tensor-first route before evaluation-zero conjugation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetSmallRectangle.l\
    ean:53"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetSmallLeftRoute :=
  isoSquareRoute (forgetSupportedTensorSmallIso p)
    (evaluationForgetSmallComparisonIso (X := op A.right) A.hom)

/-- The actual support-forgetting-first route before evaluation-zero conjugation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetSmallRectangle.l\
    ean:58"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetSmallRightRoute :=
  isoSquareRoute (evaluationForgetSmallComparisonIso (X := op B.right) B.hom)
    (forgetAmbientTensorSmallIso p)

set_option maxHeartbeats 800000 in
-- The unchanged full rectangle needs more elaboration steps on native geometric zero rebases.
/-- Common-universe transport preserves the complete independently normalized rectangle. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetSmallRectangle.l\
    ean:63"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
theorem tensorForgetSmallRectangle_hom :
    whiskerLeft (evaluationSmall (X := op B.right) B.hom)
        (tensorForgetModelIso p).hom ≫ (tensorForgetSmallRightRoute p).inv =
      (tensorForgetSmallLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙ GlobalSectionChangeIndex.evaluationSmall
          (op A.right)) (forgetReindexInputSquare p)) :=
  asSmallRouteRectangle (forgetSupportedTensorNormalizedIso p)
    (forgetNormalizedIso (X := op A.right) A.hom)
    (forgetNormalizedIso (X := op B.right) B.hom)
    (forgetAmbientTensorNormalizedIso p) (tensorForgetNormalizedIso p)
    (forgetReindexInputSquare p) (tensorForgetNormalizedRectangle_hom p)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
