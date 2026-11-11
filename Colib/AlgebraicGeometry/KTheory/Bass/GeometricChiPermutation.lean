/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiComparisonCells

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

/-- The actual geometric comparison retains the complete two-cone permutation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiPermutation.lean:24"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem comparison (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (GeometricSeedCospan.chiGeom F).app X =
      LoopFactor.coneStrength ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) ≫
        parameterLoopingMap (permutation F X).hom := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  induction z using Cell.inductionOn
    (((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj (square X)) n with
  | hTarget γ => exact comparison_target F X n γ
  | hUpper r γ => exact comparison_upper F X n r γ
  | hLower r γ => exact comparison_lower F X n r γ
  | hOverlap r s γ => exact comparison_overlap F X n r s γ

end KTheory.Bass.GeometricChiPermutation

namespace KTheory.Bass.GeometricChiPermutation

attribute [colib_tag "COL-0582"] comparison

end KTheory.Bass.GeometricChiPermutation
