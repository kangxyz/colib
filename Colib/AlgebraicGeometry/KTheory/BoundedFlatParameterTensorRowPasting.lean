/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorModelUnit
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationPasting

/-! # The actual ambient tensor/evaluation first-row prism

Both sides use the original forward unit. The comparison retains the tensor unitor, evaluation
pseudonaturality and selected-zero normalizations as its actual endpoint path. The genuine row
coordinate is retained by the row spectrum target rather than replaced by K of the row category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
      CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- Evaluate the original internal forward unit on the actual coefficient Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPasting.lean:29"
  "adaptation" "Original endpoint-relative first-row pasting with independent coordinates."]
def internalModelUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (internalModelMap Q X).hom.toFunctor ⟶ (internalModelMap Q X).hom.toFunctor :=
  whiskerRight
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor

/-- The original normalized genuine tensor multiplication after source evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPasting.lean:38"
  "adaptation" "Original endpoint-relative first-row pasting with independent coordinates."]
def tensorModelUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (tensorModelMap Q X).hom.toFunctor ⟶ (tensorModelMap Q X).hom.toFunctor :=
  whiskerLeft (evaluationModel (op (scheme Q X))).hom.toFunctor
    (tensorUnitPullbackModelTransformation (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X))

/-- Exact evaluation preserves the original internal unit's weak equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPasting.lean:45"
  "adaptation" "Original endpoint-relative first-row pasting with independent coordinates."]
theorem internalModelUnit_weak (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : ((ParameterModels.ambient Q).obj X).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
      X)).toRingedSpace)).obj.waldhausen.weq
      ((internalModelUnit Q X).app A) :=
  (evaluationModel (op (scheme Q (laurent.op.obj X)))).hom.isExact.weak _
    ((boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq_iso _ inferInstance)

/-- Actual source evaluation retains the true tensor crossing's weak equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPasting.lean:53"
  "adaptation" "Original endpoint-relative first-row pasting with independent coordinates."]
theorem tensorModelUnit_weak (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : ((ParameterModels.ambient Q).obj X).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
      X)).toRingedSpace)).obj.waldhausen.weq
      ((tensorModelUnit Q X).app A) :=
  tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)
    ((evaluationModel (op (scheme Q X))).hom.toFunctor.obj A)

/-- The entire endpoint-relative first-row prism, preserving both original zero normalizations. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPasting.lean:62"
  "adaptation" "Original endpoint-relative first-row pasting with independent coordinates."]
def tensorRowPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationPasting
    (F := internalModelMap Q X) (G := internalModelMap Q X)
    (G' := tensorModelMap Q X) (H := tensorModelMap Q X)
    (internalModelUnit Q X) (internalTensorModelIso Q X).hom
    (internalTensorModelIso Q X).hom (tensorModelUnit Q X)
    (internalModelUnit_weak Q X)
    (fun _ => (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      (scheme Q (laurent.op.obj X)).toRingedSpace)).obj.waldhausen.weq_iso _ inferInstance)
    (fun _ => (asSmallCategory (boundedAboveFlatPerfectWaldhausen
      (scheme Q (laurent.op.obj X)).toRingedSpace)).obj.waldhausen.weq_iso _ inferInstance)
    (tensorModelUnit_weak Q X) (internalTensorModelIso_unit Q X)

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
