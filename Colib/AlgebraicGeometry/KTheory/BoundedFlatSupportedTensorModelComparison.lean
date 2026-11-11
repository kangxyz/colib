/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedEvaluationModel
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairModel
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallModel

/-!
# Actual supported tensor evaluation with both selected-zero
      comparisons

The comparison uses the original supported tensor unitor and the
      original supported geometric
reindex/evaluation isomorphism. All maps remain between the true
      supported Models.
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
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- The original supported tensor unitor after genuine pair pullback.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelComparison.le\
    an:32"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
def tensorPairUnitor : tensorSupportedPairFunctor p ≅ boundedAboveFlatPerfectSupportedPullback p :=
  isoWhiskerLeft (boundedAboveFlatPerfectSupportedPullback p)
    (boundedAboveFlatPerfectSupportedTensorUnitIso A.hom)

/-- Retain the actual unitor and geometric evaluation transition in one full
      supported iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelComparison.le\
    an:37"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
def tensorEvaluationIso :
    boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom ⋙
      tensorSupportedPairFunctor p ≅
      (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙
        boundedAboveFlatGlobalSupportedEvaluation (X := op A.right) A.hom :=
  isoWhiskerLeft _ (tensorPairUnitor p) ≪≫ boundedAboveFlatGlobalSupportedPairReindexEvaluationIso p

/-- Genuine tensor pullback after the actual supported evaluation
      Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelComparison.le\
    an:44"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
def tensorModelMap :=
  evaluationModel (X := op B.right) B.hom ≫ tensorSupportedPairModelMap p

/-- Original supported reindexing followed by actual target
      evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelComparison.le\
    an:48"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
def internalModelMap :=
  boundedAboveFlatGlobalSupportedPairModelMap p ≫ evaluationModel (X := op A.right) A.hom

/-- Original common-universe transport retains the tensor functor's own zero rebase. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelComparison.le\
    an:52"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
def tensorMiddleIso :
    ((boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙
      boundedAboveFlatGlobalSupportedEvaluation (X := op A.right) A.hom) ⋙ AsSmall.up ≅
    evaluationSmall (X := op B.right) B.hom ⋙
      (tensorSupportedPairModelMap p).hom.toFunctor :=
  asSmallWhiskerIso (boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom)
    ((boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙
      boundedAboveFlatGlobalSupportedEvaluation (X := op A.right) A.hom)
    (tensorSupportedPairFunctor p) _ (tensorEvaluationIso p).symm
    (tensorSupportedPairNormalization p)

/-- Both supported evaluation normalizations are retained in the
      actual Model comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelComparison.le\
    an:64"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
def internalTensorModelIso : (internalModelMap p).hom.toFunctor ≅ (tensorModelMap p).hom.toFunctor
      :=
  isoWhiskerLeft (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor
      (evaluationNormalizationIso (X := op A.right) A.hom).symm ≪≫
    (Functor.associator (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor
      (boundedAboveFlatGlobalSupportedEvaluation (X := op A.right) A.hom) AsSmall.up).symm
      ≪≫
    tensorMiddleIso p ≪≫
    isoWhiskerRight (evaluationNormalizationIso (X := op B.right) B.hom) _

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
