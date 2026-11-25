/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartTargetSeams

/-!
# The original ten-node raw square in the whole seed postproduct

The two complete polynomial evaluation nodes recover the original ten-node product, including
every anchor. Its whole characteristic map therefore retains both original independent times.
The initial row retains the complete chart normalization word, and the terminal evaluation
row meets the actual positive raw descent boundary.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen.IteratedS Topology SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostRows
open GlobalSectionChangeIndex CommonReferenceNerve

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
local notation "F" => InputSeedEvaluationCarrier.polyRef Y
local notation "G" => InputSeedCarrier.laurentRef g

/-- All ten complete product nodes are the original raw chart product nodes. -/
theorem grid_nodes :
    FiniteParameter.gridNodes F G (InputSeedPostProduct.productNode g)
        (InputSeedEvaluationCarrier.polynomialNodes Y) =
      InputRawChartProductNodes.nodes g plus GlobalRawBass.plus_projection := by
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (Topology.SimplexGrid.indexEquiv 1 4).surjective k
  rw [← Topology.SimplexGrid.index_eq_equiv, FiniteParameter.gridNodes_index]
  exact InputSeedPostNodes.product_nodes g i j

/-- The whole two-parameter product keeps the original evaluation and raw square clocks. -/
theorem movement_parameter (t s : I) :
    InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y t, s) =
      InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection (t, s) := by
  change InputSeedPostProduct.parameter g
    (CommonReferenceNerve.parameter F (InputSeedEvaluationCarrier.polynomialNodes Y)
      (CategoryTheory.Waldhausen.IteratedS.SimplexParameters.edge (k := 1) 0 1 t), s) = _
  rw [InputSeedPostProduct.parameter_characteristic, grid_nodes]; rfl

/-- Equality of the entire original product characteristic maps, before native evaluation. -/
theorem movement_characteristic :
    (InputSeedPostProduct.parameter g).comp
        (⟨fun z : I × I => (InputSeedEvaluationCarrier.movement Y z.1, z.2),
          by fun_prop⟩ : C(I × I, |nerve (Codiscrete (Node F))| × I)) =
      InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection := by
  ext z
  exact movement_parameter g z.1 z.2

/-- The entire initial row retains all five original complete chart normalization nodes. -/
theorem initial_nodes (i : Fin 5) :
    InputSeedPostProduct.productNode g (InputSeedEvaluationCarrier.polynomialNodes Y 0) i =
      InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection
        (InputChartNormalizationNodes.normalizationRow i) :=
  (InputSeedPostNodes.product_nodes g 0 i).trans
    (InputChartTargetSeams.raw_nodes g plus GlobalRawBass.plus_projection i)

/-- The initial row is the original reversed-first and forward-second chart path. -/
theorem initial_parameter (s : I) :
    InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y 0, s) =
      (((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 1 2).trans
        (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 2 4)).symm.trans
          ((InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 1 5).trans
            (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 5 7))) s :=
  (movement_parameter g 0 s).trans
    (InputChartTargetSeams.raw_parameter g plus GlobalRawBass.plus_projection s)

/-- The entire terminal row is the unchanged positive raw descent boundary. -/
theorem terminal_parameter (s : I) :
    InputSeedPostProduct.parameter g (InputSeedEvaluationCarrier.movement Y 1, s) =
      InputRawDesc.parameter g (s, 0) :=
  (movement_parameter g 1 s).trans (InputRawChartProductNodes.plus_attachment g s)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostRows
