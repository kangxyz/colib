/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorInitialCell
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# The genuine tensor cell returned to the original parameter Model

Both the actual tensor multiplication and its evaluation/unitor endpoint path pass
through the exact categorical inverse. The two-cylinder first-row realization is
retained, and its complete endpoint-relative prism now lies in the original Model's
row target. This is the common target needed before the original Bass inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
      CategoryTheory.Functor.IdentityAutomorphism
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GlobalSupportedSection

/-- The exact inverse preserves weakness of the original tensor multiplication. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedCell.lean:34"
  "adaptation" "Original genuine tensor cell returned by the exact categorical inverse."]
theorem returnedTensorUnit_weak (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : ((ParameterModels.ambient Q).obj X).obj.Obj) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq
      ((returnedTensorUnit Q X).app A) :=
  (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).hom.isExact.weak _
    (tensorModelUnit_weak Q X A)

/-- The independently realized tensor cell after the actual exact inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedCell.lean:42"
  "adaptation" "Original genuine tensor cell returned by the exact categorical inverse."]
def returnedTensorCell (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationSpectrumHomotopy (F := returnedTensorModel Q X)
    (G := returnedTensorModel Q X) (returnedTensorUnit Q X) (returnedTensorUnit_weak Q X)

/-- The original unit of evaluation and genuine tensor unitor give this actual moving endpoint.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedCell.lean:48"
  "adaptation" "Original genuine tensor cell returned by the exact categorical inverse."]
def returnedMovement (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationSpectrumHomotopy
    (F := boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op) (G :=
      returnedTensorModel Q X)
    (returnedTensorIso Q X).hom
    (fun _ => (boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq_iso _
      inferInstance)

/-- The real first-row prism intertwines the internal cell and the returned genuine tensor cell.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedCell.lean:57"
  "adaptation" "Original genuine tensor cell returned by the exact categorical inverse."]
def returnedPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((initialCell Q X).trans (returnedMovement Q X)).RelHomotopy
      ((returnedMovement Q X).trans (returnedTensorCell Q X)) := by
  let J := rowTransformationPasting
    (F := boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op)
    (G := boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op)
    (G' := returnedTensorModel Q X) (H := returnedTensorModel Q X)
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
    (returnedTensorIso Q X).hom (returnedTensorIso Q X).hom (returnedTensorUnit Q X)
    (fun _ => (boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq_iso _
      inferInstance)
    (fun _ => (boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq_iso _
      inferInstance)
    (fun _ => (boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq_iso _
      inferInstance)
    (returnedTensorUnit_weak Q X) (returnedTensorIso_unit Q X)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl

/-- Returning evaluation preserves the whole genuine tensor cell at the original unit time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedCell.lean:84"
  "adaptation" "Original genuine tensor cell returned by the exact categorical inverse."]
theorem returnedTensorCell_at (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (returnedTensorCell Q X).at t =
      (rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).at t ≫
        rowLoopMap (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))) :=
  rowTransformationSpectrumHomotopy_postcomp_at (tensorModelUnit Q X)
    (tensorModelUnit_weak Q X)
    (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))) t

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0550"] returnedPasting
attribute [colib_tag "COL-0550"] returnedTensorCell_at

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
