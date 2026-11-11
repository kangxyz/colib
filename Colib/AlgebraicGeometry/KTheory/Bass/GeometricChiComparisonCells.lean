/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiCellEvaluation
public import Colib.AlgebraicGeometry.KTheory.Bass.LoopFactorCells

/-! # The whole geometric comparison and original double-cone permutation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u w
namespace KTheory.Bass.GeometricChiPermutation
open GeometricConeInterchange

/-- The whole target loop cell agrees, at every loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiComparisonCells.lean:25"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem comparison_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (γ : Path (((coneFunctor.obj F).obj (laurent.op.obj X)).point n)
      (((coneFunctor.obj F).obj (laurent.op.obj X)).point n)) :
    ((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.target (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n γ) =
      ((LoopFactor.coneStrength
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) ≫
          parameterLoopingMap (permutation F X).hom).map n)
        (Cell.target (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
          (square X)) n γ) := by
  apply Path.ext
  funext t
  exact (chi_target F X n γ t).trans
    ((target_scalar F X n (γ t)).trans
      (congrArg ((permutation F X).hom.map n)
        (LoopFactor.coneStrength_target
          ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n γ t)).symm)

/-- The whole upper loop cell agrees, at every loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiComparisonCells.lean:46"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem comparison_upper (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (γ : Path (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)
      (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)) :
    ((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.upper (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n r γ) =
      ((LoopFactor.coneStrength
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) ≫
          parameterLoopingMap (permutation F X).hom).map n)
        (Cell.upper (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
          (square X)) n r γ) := by
  apply Path.ext
  funext t
  exact (chi_upper F X n r γ t).trans
    ((upper_scalar F X n r (γ t)).trans
      (congrArg ((permutation F X).hom.map n)
        (LoopFactor.coneStrength_upper
          ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r γ t)).symm)

/-- The whole lower loop cell agrees, at every loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiComparisonCells.lean:67"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem comparison_lower (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (γ : Path (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)
      (((coneFunctor.obj F).obj (polynomial.op.obj X)).point n)) :
    ((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.lower (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n r γ) =
      ((LoopFactor.coneStrength
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) ≫
          parameterLoopingMap (permutation F X).hom).map n)
        (Cell.lower (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
          (square X)) n r γ) := by
  apply Path.ext
  funext t
  exact (chi_lower F X n r γ t).trans
    ((lower_scalar F X n r (γ t)).trans
      (congrArg ((permutation F X).hom.map n)
        (LoopFactor.coneStrength_lower
          ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r γ t)).symm)

/-- The whole overlap loop cell agrees, at every loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiComparisonCells.lean:88"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem comparison_overlap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s : unitInterval)
    (γ : Path (((coneFunctor.obj F).obj (X)).point n)
      (((coneFunctor.obj F).obj (X)).point n)) :
    ((GeometricSeedCospan.chiGeom F).app X).map n
      (Cell.overlap (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
        (square X)) n r s γ) =
      ((LoopFactor.coneStrength
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) ≫
          parameterLoopingMap (permutation F X).hom).map n)
        (Cell.overlap (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj
          (square X)) n r s γ) := by
  apply Path.ext
  funext t
  exact (chi_overlap F X n r s γ t).trans
    ((overlap_scalar F X n r s (γ t)).trans
      (congrArg ((permutation F X).hom.map n)
        (LoopFactor.coneStrength_overlap
          ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s γ t)).symm)

end KTheory.Bass.GeometricChiPermutation
