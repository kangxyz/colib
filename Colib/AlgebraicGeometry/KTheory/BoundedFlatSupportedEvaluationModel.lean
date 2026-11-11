/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedStructure
public import Colib.CategoryTheory.Waldhausen.AsSmall.Whiskering
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-!
# Original chosen-zero evaluation of supported sections

The actual supported evaluation is first placed in the original common universe. Only its
chosen zero is normalized, with the complete original comparison isomorphism retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- Evaluation in the original common universe, with the actual supported predicate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationModel.le\
    an:29"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationSmall :
    (boundedAboveFlatGlobalSupportedSectionModel j).obj.Obj ⥤ AsSmall.{0}
      ((boundedAboveFlatPerfectSupported j).FullSubcategory) :=
  boundedAboveFlatGlobalSupportedEvaluation j ⋙ AsSmall.up

/-- The original supported evaluation is exact after universe transport. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationModel.le\
    an:34"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
theorem evaluationSmall_exact :
    IsExact (boundedAboveFlatGlobalSupportedSectionModel j).obj.waldhausen.cof
      (boundedAboveFlatGlobalSupportedSectionModel j).obj.waldhausen.weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.weq (evaluationSmall j) :=
  (boundedAboveFlatGlobalSupportedEvaluation_exact j).comp
    (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall_up_exact

/-- The evaluated original chosen zero has its unique actual zero comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationModel.le\
    an:42"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationZeroIso :
    (evaluationSmall j).obj (boundedAboveFlatGlobalSupportedSectionModel j).obj.waldhausen.zero ≅
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.zero :=
  ((evaluationSmall_exact j).zero (boundedAboveFlatGlobalSupportedSectionModel
      j).obj.waldhausen.isZero).iso
    (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.isZero

/-- The actual supported evaluation as a chosen-zero Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationModel.le\
    an:49"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationModel : boundedAboveFlatGlobalSupportedSectionModel j ⟶
    asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j) :=
  ⟨⟨CategoryTheory.rebaseFunctor (evaluationSmall j)
      (boundedAboveFlatGlobalSupportedSectionModel j).obj.waldhausen.zero
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.zero (evaluationZeroIso j),
    (evaluationSmall_exact j).rebase⟩, CategoryTheory.rebaseFunctor_obj_base _ _ _ _⟩

/-- The whole original chosen-zero normalization isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationModel.le\
    an:56"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationNormalizationIso : evaluationSmall j ≅ (evaluationModel j).hom.toFunctor :=
  CategoryTheory.rebaseFunctorIso _ _ _ (evaluationZeroIso j)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
