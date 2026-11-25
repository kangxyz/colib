/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartReference

/-!
# Exact full-node selection of the original two charts

The common eight-node descent diagram selects both original five-node charts, including
the actual source and total reference isomorphisms shared by the two charts.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
variable (X : Scheme.{u})

/-- All five positive-chart nodes retain their complete original reference isomorphisms. -/
theorem plus_nodes (i : Fin 5) :
    InputChartSimplex.nodes X (InputChartSimplex.plusFace.toOrderHom i) =
      InputChartSimplex.chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) i := by
  fin_cases i <;> rfl

/-- The inverse chart shares precisely the original source and total dependent nodes. -/
theorem minus_nodes (i : Fin 5) :
    InputChartSimplex.nodes X (InputChartSimplex.minusFace.toOrderHom i) =
      InputChartSimplex.chartNodes X (minus.app X) (GlobalRawBass.minus_projection X) i := by
  fin_cases i
  · exact (InputChartSimplex.chartNodes_zero X (plus.app X)
      (GlobalRawBass.plus_projection X)).trans
        (InputChartSimplex.chartNodes_zero X (minus.app X)
          (GlobalRawBass.minus_projection X)).symm
  · exact (InputChartSimplex.chartNodes_one X (plus.app X)
      (GlobalRawBass.plus_projection X)).trans
        (InputChartSimplex.chartNodes_one X (minus.app X)
          (GlobalRawBass.minus_projection X)).symm
  · rfl
  · rfl
  · rfl

/-- Every barycentric point of the positive chart is its original nerve characteristic map. -/
theorem plus_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
      (StdSimplex.map InputChartSimplex.plusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X)
      (InputChartSimplex.chartNodes X (plus.app X) (GlobalRawBass.plus_projection X)) z := by
  rw [CommonReferenceNerve.parameter_face]
  exact congrArg (fun N => CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) N z)
    (funext (plus_nodes X))

/-- Every inverse-chart point uses full shared nodes, before native evaluation. -/
theorem minus_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
      (StdSimplex.map InputChartSimplex.minusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X)
      (InputChartSimplex.chartNodes X (minus.app X) (GlobalRawBass.minus_projection X)) z := by
  rw [CommonReferenceNerve.parameter_face]
  exact congrArg (fun N => CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) N z)
    (funext (minus_nodes X))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartReference
