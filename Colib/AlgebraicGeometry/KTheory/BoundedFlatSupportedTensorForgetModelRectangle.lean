/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorForgetSmallRectangle
public import Colib.CategoryTheory.Functor.IsoRouteRectangle

/-! # The complete original tensor/forgetting Model rectangle

The raw supported tensor/forgetting comparison is normalized independently and lifted through
the genuine common-universe functors. The complete Model rectangle retains both endpoint
evaluation normalizations and the intermediate normalization on each actual route.
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

/-- The original supported tensor Model edge is the genuine small edge at its two corners. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetModelRectangle.l\
    ean:31"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
theorem internalTensorModelIso_forgetSmall :
    internalTensorModelIso p = isoSquareConjugate (forgetSupportedTensorSmallIso p)
      (evaluationNormalizationIso (X := op B.right) B.hom)
      (evaluationNormalizationIso (X := op A.right) A.hom) := by
  simp only [internalTensorModelIso, isoSquareConjugate, forgetSupportedTensorSmallIso,
    tensorMiddleIso, asSmallWhiskerIso, forgetSupportedTensorNormalizedIso, Iso.trans_assoc]

/-- The ambient tensor Model edge retains the two original ambient evaluation normalizations. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetModelRectangle.l\
    ean:39"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def forgetAmbientTensorModelIso :=
  isoSquareConjugate (forgetAmbientTensorSmallIso p)
    (GlobalSectionChangeIndex.evaluationNormalizationIso (op B.right))
    (GlobalSectionChangeIndex.evaluationNormalizationIso (op A.right))

/-- The original supported-tensor-first route with every actual evaluation normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetModelRectangle.l\
    ean:45"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetModelLeftRoute :=
  isoSquareRoute (internalTensorModelIso p)
    (evaluationForgetModelComparisonIso (X := op A.right) A.hom)

/-- The original support-forgetting-first route with every actual evaluation normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetModelRectangle.l\
    ean:50"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetModelRightRoute :=
  isoSquareRoute (evaluationForgetModelComparisonIso (X := op B.right) B.hom)
    (forgetAmbientTensorModelIso p)

/-- The whole Model-level rectangle retains the original tensor and all support-forgetting paths. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetModelRectangle.l\
    ean:55"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
theorem tensorForgetModelRectangle_hom :
    whiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
        (tensorForgetModelIso p).hom ≫ (tensorForgetModelRightRoute p).inv =
      (tensorForgetModelLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel (op A.right)).hom.toFunctor)
          (forgetReindexInputSquare p)) := by
  unfold tensorForgetModelLeftRoute tensorForgetModelRightRoute
  rw [internalTensorModelIso_forgetSmall]
  unfold evaluationForgetModelComparisonIso forgetAmbientTensorModelIso
  rw [isoSquareRoute_conjugate, isoSquareRoute_conjugate]
  exact isoSquareConjugate_rectangle (tensorForgetSmallLeftRoute p)
    (tensorForgetSmallRightRoute p) (tensorForgetModelIso p) (forgetReindexInputSquare p)
    (evaluationNormalizationIso (X := op B.right) B.hom)
    (GlobalSectionChangeIndex.evaluationNormalizationIso (op A.right))
    (tensorForgetSmallRectangle_hom p)

/-- Equality of the full specified Model isomorphism routes, including their source transport. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetModelRectangle.l\
    ean:73"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
theorem tensorForgetModelRectangle :
    isoWhiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
        (tensorForgetModelIso p) ≪≫ (tensorForgetModelRightRoute p).symm =
      (tensorForgetModelLeftRoute p).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel (op A.right)).hom.toFunctor)
          (forgetReindexInputSquare p)) := by
  apply Iso.ext
  exact tensorForgetModelRectangle_hom p

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
