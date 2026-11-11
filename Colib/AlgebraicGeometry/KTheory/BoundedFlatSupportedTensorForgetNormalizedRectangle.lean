/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorForgetRawRectangle
public import Colib.CategoryTheory.Functor.IsoRouteTargetNormalization
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitIteratedPrism

/-! # The tensor/forgetting rectangle through all original geometric zero rebases

The independently defined supported tensor/forgetting square is surrounded by the four actual
chosen-zero normalization isomorphisms. Its two complete evaluation routes retain these paths.
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

/-- Normalize the supported tensor leg and then the original target support inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:31"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetLeftNormalization :=
  isoWhiskerRight (tensorSupportedPairNormalization p)
      (tensorCoefficientSupportedForget A.hom) ≪≫
    isoWhiskerLeft (tensorSupportedPairNormalizedFunctor p)
      (forgetRawNormalization (X := op A.right) A.hom)

/-- Normalize the original source support inclusion and then the ambient tensor leg. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:38"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetRightNormalization :=
  isoWhiskerRight (forgetRawNormalization (X := op B.right) B.hom)
      (boundedAboveFlatPerfectTensorUnitPullback p.right) ≪≫
    isoWhiskerLeft _ (tensorUnitPullbackNormalization p.right)

/-- The actual raw forgetting square surrounded by all four original zero rebases. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:44"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetNormalizedIso :=
  (tensorForgetLeftNormalization p).symm ≪≫ tensorSupportedPairForgetIso p ≪≫
    tensorForgetRightNormalization p

/-- The independently normalized supported tensor/evaluation edge. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:49"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def forgetSupportedTensorNormalizedIso :=
  (tensorEvaluationIso p).symm ≪≫
    isoWhiskerLeft (boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom)
      (tensorSupportedPairNormalization p)

/-- The independently normalized ambient tensor/evaluation edge. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:55"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def forgetAmbientTensorNormalizedIso :=
  (GlobalSectionChangeIndex.tensorEvaluationIso p.right).symm ≪≫
    isoWhiskerLeft (boundedAboveFlatGlobalSectionEvaluation (op B.right))
      (tensorUnitPullbackNormalization p.right)

/-- The actual inclusion/evaluation edge with its own geometric zero rebase. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:61"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def forgetNormalizedIso {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] :=
  evaluationForgetIso j ≪≫ isoWhiskerLeft (boundedAboveFlatGlobalSupportedEvaluation j)
      (forgetRawNormalization j)

/-- The complete supported-tensor-first normalized route. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:66"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetNormalizedLeftRoute :=
  isoSquareRoute (forgetSupportedTensorNormalizedIso p)
    (forgetNormalizedIso (X := op A.right) A.hom)

/-- The complete support-forgetting-first normalized route. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:71"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
def tensorForgetNormalizedRightRoute :=
  isoSquareRoute (forgetNormalizedIso (X := op B.right) B.hom)
    (forgetAmbientTensorNormalizedIso p)

/-- All four original geometric zero comparisons preserve the whole two-route rectangle. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetNormalizedRectan\
    gle.lean:76"
  "adaptation" "Original complete normalized, AsSmall and Model tensor-forgetting rectangles."]
theorem tensorForgetNormalizedRectangle_hom :
    whiskerLeft (boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom)
        (tensorForgetNormalizedIso p).hom ≫ (tensorForgetNormalizedRightRoute p).inv =
      (tensorForgetNormalizedLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙ boundedAboveFlatGlobalSectionEvaluation (op A.right))
          (forgetReindexInputSquare p)) := by
  unfold tensorForgetNormalizedLeftRoute tensorForgetNormalizedRightRoute
    forgetSupportedTensorNormalizedIso forgetAmbientTensorNormalizedIso forgetNormalizedIso
  rw [isoSquareRoute_targetNormalization, isoSquareRoute_targetNormalization]
  exact isoSquareTargetNormalization_rectangle
    (isoSquareRoute (tensorEvaluationIso p).symm
      (evaluationForgetIso (X := op A.right) A.hom))
    (isoSquareRoute (evaluationForgetIso (X := op B.right) B.hom)
      (GlobalSectionChangeIndex.tensorEvaluationIso p.right).symm)
    (tensorSupportedPairForgetIso p) (forgetReindexInputSquare p)
    (tensorForgetLeftNormalization p) (tensorForgetRightNormalization p)
    (tensorForgetRawRectangle_hom p)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
