/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorEvaluationRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitIteratedPrism
public import Colib.CategoryTheory.Waldhausen.AsSmall.Whiskering

/-!
# The actual tensor and internal coefficient Model comparison

The original tensor unitor and evaluation transition are transported through both selected-zero
normalizations. The result compares actual Model functors and is not a strict evaluation square.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The normalized genuine tensor map after actual parameter evaluation. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelComparison.lean:28"
  "adaptation" "Original actual tensor comparison and both selected-zero normalizations."]
def tensorModelMap (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  evaluationModel (op (scheme Q X)) ≫ tensorUnitPullbackModelMap (coefficientMap Q X)

/-- The original coefficient map followed by actual target evaluation. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelComparison.lean:32"
  "adaptation" "Original actual tensor comparison and both selected-zero normalizations."]
def internalModelMap (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op ≫
    evaluationModel (op (scheme Q (laurent.op.obj X)))

/-- Common-universe transport of the genuine tensor comparison and its original raw rebase. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelComparison.lean:37"
  "adaptation" "Original actual tensor comparison and both selected-zero normalizations."]
def tensorMiddleIso (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (op (scheme Q (laurent.op.obj X)))) ⋙ AsSmall.up ≅
    evaluationSmall (op (scheme Q X)) ⋙
      (tensorUnitPullbackModelMap (coefficientMap Q X)).hom.toFunctor :=
  asSmallWhiskerIso (boundedAboveFlatGlobalSectionEvaluation (op (scheme Q X)))
    ((boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (op (scheme Q (laurent.op.obj X))))
    (boundedAboveFlatPerfectTensorUnitPullback (coefficientMap Q X)) _
    (tensorEvaluationIso (coefficientMap Q X)).symm
    (tensorUnitPullbackNormalization (coefficientMap Q X))

/-- The complete functor isomorphism retains both actual evaluation zero normalizations. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelComparison.lean:50"
  "adaptation" "Original actual tensor comparison and both selected-zero normalizations."]
def internalTensorModelIso (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (internalModelMap Q X).hom.toFunctor ≅ (tensorModelMap Q X).hom.toFunctor :=
  isoWhiskerLeft
    (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (evaluationNormalizationIso (op (scheme Q (laurent.op.obj X)))).symm ≪≫
    (Functor.associator
      (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (boundedAboveFlatGlobalSectionEvaluation
        (op (scheme Q (laurent.op.obj X)))) AsSmall.up).symm ≪≫
    tensorMiddleIso Q X ≪≫
    isoWhiskerRight (evaluationNormalizationIso (op (scheme Q X))) _

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0547"] internalTensorModelIso

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
