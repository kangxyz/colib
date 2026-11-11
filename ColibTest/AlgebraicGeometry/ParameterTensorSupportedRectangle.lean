/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedForgetRectangle
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRectangleTest
open ParameterTensorSupportedRow GlobalSectionChangeIndex SupportedTensorEvaluation
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ)

example :
    forgetAmbientTensorModelIso (coefficientPair f X) =
      ParameterTensorEvaluationRow.internalTensorModelIso Q X :=
  forgetAmbientTensorModelIso_parameter f X

example :
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
          (forgetReindexInputSquare (coefficientPair f X))) :=
  modelEvaluationForgetRectangle_hom f X

example :
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
  modelEvaluationForgetRectangle f X

end AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRectangleTest
