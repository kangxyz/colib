/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiCell

/-! # Original outer-cell formulas for the geometric comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u v w
namespace KTheory.Bass.GeometricChiPermutation
open GeometricSquareInterchange SquareConeStrength
open PushoutStrength PushoutCofiberSquare WholeSeedCospan
open GeometricChiCell GeometricConeInterchange

/-- The whole original target cell is evaluated at the unchanged arbitrary loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCellEvaluation.lean:26"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chi_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ)
    (γ : Path (((coneFunctor.obj F).obj (laurent.op.obj X)).point n)
      (((coneFunctor.obj F).obj (laurent.op.obj X)).point n)) (t : unitInterval) :
    Path.toContinuousMap (((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.target (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n γ)) t =
      ((coneFunctor.map (targetMap F)).app X).map n
        (((GeometricConeInterchange.eta
          (laurentProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n (γ t)) := by
  have h := DoubleLaurentInclusion.chiGeom_laurentInclusion F X
  exact congrArg (fun f => Path.toContinuousMap (f.map n γ) t) h

/-- The whole original upper cell is evaluated at the unchanged arbitrary loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCellEvaluation.lean:40"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chi_upper (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval)
    (γ : Path (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)
      (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)) (t : unitInterval) :
    Path.toContinuousMap (((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.upper (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n r γ)) t =
      ((coneFunctor.map (upperMap F r)).app X).map n
        (((GeometricConeInterchange.eta
          (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n (γ t)) := by
  have h := chiAlong_upper (geometricSquare F) squareFunctor (squareInterchangeMap F)
    X n r γ
  rw [squareInterchange_polynomial] at h
  exact congrArg (fun p => Path.toContinuousMap p t) h

/-- The whole original lower cell is evaluated at the unchanged arbitrary loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCellEvaluation.lean:56"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chi_lower (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval)
    (γ : Path (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)
      (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)) (t : unitInterval) :
    Path.toContinuousMap (((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.lower (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n r γ)) t =
      ((coneFunctor.map (lowerMap F r)).app X).map n
        (((GeometricConeInterchange.eta
          (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n (γ t)) := by
  have h := chiAlong_lower (geometricSquare F) squareFunctor (squareInterchangeMap F)
    X n r γ
  change _ = (((strictDiagramFunctor squareFunctor).map (lowerMap F r)).app X).map n
    (((GeometricSquareInterchange.eta
      (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n γ) at h
  exact congrArg (fun p => Path.toContinuousMap p t) h

/-- Both original overlap parameters and the arbitrary loop time remain independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCellEvaluation.lean:74"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chi_overlap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r s : unitInterval)
    (γ : Path (((coneFunctor.obj F).obj X).point n)
      (((coneFunctor.obj F).obj X).point n)) (t : unitInterval) :
    Path.toContinuousMap (((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.overlap (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n r s γ)) t =
      ((coneFunctor.map (overlapMap F r s)).app X).map n (γ t) := by
  have h := chiAlong_overlap (geometricSquare F) squareFunctor (squareInterchangeMap F)
    X n r s γ
  rw [squareInterchange_base] at h
  exact congrArg (fun p => Path.toContinuousMap p t) h

end KTheory.Bass.GeometricChiPermutation
