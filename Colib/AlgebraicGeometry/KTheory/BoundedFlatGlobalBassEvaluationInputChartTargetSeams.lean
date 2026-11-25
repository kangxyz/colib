/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartFaceSeams
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartNormNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputTargetFace

public import Colib.Topology.Path.ScalarPathCells

/-!
# The actual target descent seams of both chart squares

The complete original raw square rows are identified through their shared evaluation-cut
node. Their unchanged reverse-forward words then give both full target-face seams, including
the outer half clock and the independent original raw-square clock.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartTargetSeams
open GlobalSectionChangeIndex Topology Path.CarrierHalfPaths
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- Every original initial product node has the complete attached commuting-chart anchor. -/
theorem raw_nodes (i : Fin 5) :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (0, i)) =
      InputChartSquareParameter.nodes g k hk (InputChartNormalizationNodes.normalizationRow i) :=
  ModelSimplex.pre_families_match (InputMixedDesc.sourceMap g)
    (InputNormalizationPrism.firstSource (projection.app Y))
    (InputRawChartRows.squareSource g k) (InputRawChartRows.squareNodes g k)
    (InputChartNormalizationNodes.product_nodes g k hk)
    (InputChartNormalizationNodes.chart_nodes g k hk) 2
    ((InputRawPastedSeam.column_initial_node g k hk).trans
      (InputChartFaceNodes.post_target_node g k hk).symm) i

private def normalizationFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨InputChartNormalizationNodes.normalizationRow, by decide⟩

/-- The entire raw product's initial characteristic row is the original normalization face. -/
private theorem raw_characteristic (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputRawChartProductNodes.nodes g k hk)
      (StdSimplex.map (SimplexGrid.rowFace 1 4 0).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartSquareParameter.nodes g k hk)
      (StdSimplex.map normalizationFace.toOrderHom z) :=
  CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputChartSquareParameter.nodes g k hk) (InputRawChartProductNodes.nodes g k hk)
    normalizationFace (SimplexGrid.rowFace 1 4 0) (raw_nodes g k hk) z

private theorem raw_scalar (s : unitInterval) :
    StdSimplex.map normalizationFace.toOrderHom
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
      (((binaryPath 1 2 4).symm.trans (binaryPath 1 5 7)) :
        Path (StdSimplex.single 4 : StdSimplex ℝ (Fin 8)) (StdSimplex.single 7)) s := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [BoundedFlatPerfectNativeSquareFiveSimplex.parameter, path_lower, path_lower]
    exact map_binaryPath normalizationFace 0 1 2 (unitInterval.symm t)
  · rw [BoundedFlatPerfectNativeSquareFiveSimplex.parameter, path_upper, path_upper]
    exact map_binaryPath normalizationFace 0 3 4 t

/-- The original raw square path keeps its reversed-first and forward-second half clocks. -/
theorem raw_parameter (s : unitInterval) :
    InputRawChartProductNodes.parameter g k hk (0, s) =
      (((InputChartSquareParameter.edge g k hk 1 2).trans
        (InputChartSquareParameter.edge g k hk 2 4)).symm.trans
          ((InputChartSquareParameter.edge g k hk 1 5).trans
            (InputChartSquareParameter.edge g k hk 5 7))) s := by
  change CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputRawChartProductNodes.nodes g k hk) (InputRawSquareProduct.parameter (0, s)) = _
  rw [InputRawSquareProduct.parameter_evaluation_zero, raw_characteristic, raw_scalar]
  change ((((binaryPath (k := 7) 1 2 4).symm.trans (binaryPath 1 5 7))).map
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartSquareParameter.nodes g k hk)).continuous) s = _
  simp only [binaryPath, Path.map_trans, ← Path.map_symm, InputChartSquareParameter.edge]

/-- The whole positive target seam retains both original input and evaluation clocks. -/
theorem plus (r : unitInterval) :
    InputTargetFace.parameter g (r, 0) =
      InputChartSquareParameter.parameter g plus GlobalRawBass.plus_projection (1, r) := by
  rw [InputChartSquareParameter.parameter_one]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [InputTargetFace.parameter_lower, path_lower]
    exact InputChartFaceSeams.post_plus g t
  · rw [InputTargetFace.parameter_upper, path_upper, InputRawPastedParameter.parameter_left]
    exact raw_parameter g AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.plus
      GlobalRawBass.plus_projection t

/-- The inverse target seam keeps its distinct original raw square and complete references. -/
theorem minus (r : unitInterval) :
    InputTargetFace.parameter g (r, 1) =
      InputChartSquareParameter.parameter g minus GlobalRawBass.minus_projection (1, r) := by
  rw [InputChartSquareParameter.parameter_one]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [InputTargetFace.parameter_lower, path_lower]
    exact InputChartFaceSeams.post_minus g t
  · rw [InputTargetFace.parameter_upper, path_upper, InputRawPastedParameter.parameter_right]
    exact raw_parameter g AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.minus
      GlobalRawBass.minus_projection t

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartTargetSeams
