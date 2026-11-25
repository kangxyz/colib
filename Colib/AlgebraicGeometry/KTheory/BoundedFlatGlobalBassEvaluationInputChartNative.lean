/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartSimplex
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputParameter

/-!
# Both original global evaluation chart surfaces in one carrier

The actual positive and inverse pastings occupy their whole original scalar faces of the
common eight-node diagram. All normalization and evaluation clock subdivisions are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSimplex
variable (X : Scheme.{u})

private theorem chart_native (k : laurent.obj X ⟶ polynomial.obj X)
    (h : k ≫ projection.app X = GlobalRawBass.laurentProjection.app X)
    (α : ⦋4⦌ ⟶ ⦋7⦌)
    (hface : (simplex X).face α = InputSimplex.simplex k (projection.app X)) :
    HomotopyLift (simplex X) (InputParameter.chart α) (chartPasting X k h) := by
  have hl := InputParameter.reindex_native α _ (simplex X) hface _ _
    (HomotopyLift.symm _ (InputSimplex.composition_native k (projection.app X)))
  intro n r s x
  exact hl n r s x

/-- Every point of the actual positive chart is preserved in the common diagram. -/
theorem plus_native :
    HomotopyLift (simplex X) (InputParameter.chart plusFace)
      (chartPasting X (plus.app X) (GlobalRawBass.plus_projection X)) :=
  chart_native X _ _ _ (plus_face X)

/-- The inverse chart retains its own full normalization and evaluation surface. -/
theorem minus_native :
    HomotopyLift (simplex X) (InputParameter.chart minusFace)
      (chartPasting X (minus.app X) (GlobalRawBass.minus_projection X)) :=
  chart_native X _ _ _ (minus_face X)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSimplex
