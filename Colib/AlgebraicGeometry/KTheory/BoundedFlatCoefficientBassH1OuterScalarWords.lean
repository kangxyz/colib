/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1Old62Bottom
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1ChartProduct

/-! Exact whole scalar outer chart words, retaining the original pause, speeds and reversals.
Adapted from Quillen's `H1OuterScalarWords.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Topology FundamentalGroupoid.OpenCover
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open BoundedFlatCoefficientBassH0Merged

/--
The five-vertex word for the first half of the old outer chart endpoint, in its reversed binary-
path order.
-/
def outerFirstWordIndex : Fin 5 → Fin 18 := ![5, 7, 17, 6, 13]
/--
The five-vertex word for the second half of the old outer chart endpoint, in its original scalar
path order.
-/
def outerProductWordIndex : Fin 5 → Fin 18 := ![9, 12, 13, 10, 11]

/-- The original terminal pause leaves the whole target chart path literally unchanged. -/
theorem old_chart_one_parameter (s : unitInterval) :
    BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (1, s) =
      BoundedFlatPerfectDoubleSquareScalarPaths.originalComparisonSource s :=
  collapsed_top_eval
    (pauseRightParameter BoundedFlatPerfectDoubleSquareScalarPaths.coefficientBoundaryParameter) s

/-- The first half of the original chart endpoint has exactly this reversed two-binary word. -/
theorem old_chart_first_parameter (s : unitInterval) :
    StdSimplex.map outerFirstWordIndex (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
      BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
        (1, leftHalf s) := by
  rw [old_chart_one_parameter]
  unfold BoundedFlatPerfectDoubleSquareScalarPaths.originalComparisonSource
  rw [Path.trans_symm, trans_leftHalf, Path.trans_symm, Path.symm_symm]
  exact map_two_binary outerFirstWordIndex 0 1 2 3 4 s

/-- The other half retains the literal original second square and the original half speed. -/
theorem old_chart_second_parameter (s : unitInterval) :
    StdSimplex.map outerProductWordIndex (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
      BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
        (1, rightHalf s) := by
  rw [old_chart_one_parameter]
  unfold BoundedFlatPerfectDoubleSquareScalarPaths.originalComparisonSource
  rw [Path.trans_symm, trans_rightHalf, Path.trans_symm, Path.symm_symm]
  exact map_two_binary outerProductWordIndex 0 1 2 3 4 s

/-- The entire positive product outer edge is the actual realization-product row2 path. -/
theorem product_plus_outer_parameter (s : unitInterval) :
    BoundedFlatCoefficientBassH1Components.plusParameter.{u} (s, 0) =
      StdSimplex.map (SimplexGrid.rowFace 4 4 2).toOrderHom
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) := by
  change SimplexGrid.parameter.{u + 1} 4 4
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter 0,
      BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = _
  rw [Path.source]
  exact SimplexGrid.parameter_row 4 4 2 _

/-- The inverse product's opposite outer edge retains its original reversed cylinder time. -/
theorem product_minus_outer_parameter (s : unitInterval) :
    BoundedFlatCoefficientBassH1Components.minusParameter.{u} (s, 1) =
      StdSimplex.map (SimplexGrid.rowFace 4 4 2).toOrderHom
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) := by
  change SimplexGrid.parameter.{u + 1} 4 4
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter (unitInterval.symm 1),
      BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = _
  rw [unitInterval.symm_one, Path.source]
  exact SimplexGrid.parameter_row 4 4 2 _

/-- The fixed old62 positive chart's complete first half has these exact scalar node labels. -/
theorem old62_plus_first_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom (outerFirstWordIndex i))))
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = plusParameter (1, leftHalf s) := by
  change _ = StdSimplex.map oldIndex
    (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
          (1, leftHalf s))))
  rw [← old_chart_first_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]; rfl

/-- The fixed old62 positive chart's entire second half retains its original scalar word. -/
theorem old62_plus_second_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom (outerProductWordIndex i))))
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = plusParameter (1, rightHalf s) := by
  change _ = StdSimplex.map oldIndex
    (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
          (1, rightHalf s))))
  rw [← old_chart_second_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]; rfl

/-- The complete first half of the separate inverse old62 chart, with its actual node labels. -/
theorem old62_minus_first_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom (outerFirstWordIndex i))))
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = minusParameter (1, leftHalf s) := by
  change _ = StdSimplex.map oldIndex
    (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
          (1, leftHalf s))))
  rw [← old_chart_first_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]; rfl

/-- The complete other half of the inverse old62 chart, without any reparameterized replacement. -/
theorem old62_minus_second_parameter (s : unitInterval) :
    StdSimplex.map (fun i ↦ oldIndex (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom (outerProductWordIndex i))))
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
        minusParameter (1, rightHalf s) := by
  change _ = StdSimplex.map oldIndex
    (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom
        (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter
          (1, rightHalf s))))
  rw [← old_chart_second_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp,
    ← StdSimplex.map_comp]; rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
