/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedEvaluationModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedForgetModel
public import Colib.CategoryTheory.Functor.IsoRouteConjugation

/-! # The original support-forgetting evaluation edge with both zero comparisons

Forgetting support uses the original full-subcategory inclusion and its original geometric
zero rebase. The evaluation comparison retains that rebase, the actual common-universe
transport, and both independently chosen evaluation-zero normalization isomorphisms.
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
open GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation
/-- The original raw evaluation-forgetting square keeps each underlying bounded-flat complex. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedEvaluationForgetModel.lean:32"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationForgetIso {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] :
    (boundedAboveFlatGlobalSupportedForget j).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation X ≅
      boundedAboveFlatGlobalSupportedEvaluation j ⋙ tensorCoefficientSupportedForget j :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The actual support inclusion with precisely its existing selected-zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedEvaluationForgetModel.lean:44"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def forgetRawNormalization :=
  CategoryTheory.rebaseFunctorIso (tensorCoefficientSupportedForget j)
    (boundedAboveFlatPerfectSupportedWaldhausen j).zero
    (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).zero
    (((tensorCoefficientSupportedForget_exact j).zero
      (boundedAboveFlatPerfectSupportedWaldhausen j).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).isZero)

/-- Original evaluated support-forgetting before the two evaluation-zero normalizations. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedEvaluationForgetModel.lean:53"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationForgetSmallComparisonIso :
    (boundedAboveFlatGlobalSupportedForget j).hom.toFunctor ⋙
      GlobalSectionChangeIndex.evaluationSmall X ≅
      evaluationSmall j ⋙ (tensorCoefficientSupportedForgetModel j).hom.toFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    asSmallWhiskerIso (boundedAboveFlatGlobalSupportedEvaluation j)
      ((boundedAboveFlatGlobalSupportedForget j).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation X)
      (tensorCoefficientSupportedForget j) _
      (evaluationForgetIso j) (forgetRawNormalization j)

/-- The genuine Model-level forgetting edge retains both actual evaluation comparisons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedEvaluationForgetModel.lean:63"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def evaluationForgetModelComparisonIso :
    (boundedAboveFlatGlobalSupportedForget j ≫ GlobalSectionChangeIndex.evaluationModel
      X).hom.toFunctor ≅
      (evaluationModel j ≫ tensorCoefficientSupportedForgetModel j).hom.toFunctor :=
  isoSquareConjugate (evaluationForgetSmallComparisonIso j)
    (evaluationNormalizationIso j) (GlobalSectionChangeIndex.evaluationNormalizationIso X)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
