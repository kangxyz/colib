/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorForgetModelRectangle
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorModelComparison

/-! # The actual parameter tensor/forgetting evaluation rectangle

The supported Laurent coefficient pair specializes the complete normalized Model rectangle.
Its ambient comparison is identified with the original parameter tensor/evaluation comparison,
so the result retains the actual parameter maps rather than a replacement ambient route.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow
open GlobalSectionChangeIndex SupportedTensorEvaluation
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ)

/-- The ambient edge is precisely the original actual parameter tensor Model comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedForgetRectang\
    le.lean:33"
  "adaptation" "Original entire supported parameter tensor and evaluation rectangle."]
theorem forgetAmbientTensorModelIso_parameter :
    forgetAmbientTensorModelIso (coefficientPair f X) =
      ParameterTensorEvaluationRow.internalTensorModelIso Q X := by
  simp only [forgetAmbientTensorModelIso, isoSquareConjugate, forgetAmbientTensorSmallIso,
    forgetAmbientTensorNormalizedIso, ParameterTensorEvaluationRow.internalTensorModelIso,
    ParameterTensorEvaluationRow.tensorMiddleIso, asSmallWhiskerIso, Iso.trans_assoc]
  rfl

/-- Forgetting genuine supported parameter tensor inputs preserves the complete Model rectangle. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedForgetRectang\
    le.lean:42"
  "adaptation" "Original entire supported parameter tensor and evaluation rectangle."]
theorem modelEvaluationForgetRectangle_hom :
    whiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair f X).right) (pair f X).hom).hom.toFunctor
        (tensorForgetModelIso (coefficientPair f X)).hom ≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair f X).right) (pair f X).hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso Q X)).inv =
      (tensorForgetModelLeftRoute (coefficientPair f X)).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair f (laurent.op.obj X)).right)).hom.toFunctor)
          (forgetReindexInputSquare (coefficientPair f X))) := by
  rw [← forgetAmbientTensorModelIso_parameter f X]
  exact tensorForgetModelRectangle_hom (coefficientPair f X)

/-- Equality of both complete original parameter Model routes, including their source transport. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorSupportedForgetRectang\
    le.lean:58"
  "adaptation" "Original entire supported parameter tensor and evaluation rectangle."]
theorem modelEvaluationForgetRectangle :
    isoWhiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair f X).right) (pair f X).hom).hom.toFunctor
        (tensorForgetModelIso (coefficientPair f X)) ≪≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair f X).right) (pair f X).hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso Q X)).symm =
      (tensorForgetModelLeftRoute (coefficientPair f X)).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair f (laurent.op.obj X)).right)).hom.toFunctor)
          (forgetReindexInputSquare (coefficientPair f X))) :=
  Iso.ext (modelEvaluationForgetRectangle_hom f X)

end AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow

attribute [colib_tag "COL-0563"] modelEvaluationForgetRectangle

end AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow
