/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterSource
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartFaceNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterEnds

/-!
# The complete terminal chart seams of the input-span square

Both full evaluation columns agree before native evaluation, including their actual reference
anchors. The entire positive and inverse seams retain their original independent time.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSeams
open InputSpanParameterWord
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private def spanChartFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩

private def chartTerminalFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![6, 7], by decide⟩

/-- The whole original evaluation side agrees through both complete finite reference nodes. -/
theorem chart_left (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (q : unitInterval) :
    chartLeft g k hk q = InputChartSquareParameter.parameter g k hk (q, 1) := by
  change CommonReferenceNerve.parameter _ _ (InputCommutingParameter.parameter (q, 0)) = _
  rw [InputCommutingParameter.parameter_left, InputChartSquareParameter.parameter_right]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputChartSquareParameter.nodes g k hk) (InputSpanParameterNodes.nodes g k hk)
    chartTerminalFace spanChartFace (fun i => by
      fin_cases i
      · exact (InputSpanParameterEdges.projection_pre_source g k hk).trans
          (InputChartFaceNodes.pre_target_node g k hk).symm
      · exact InputSpanParameterEdges.projection_chart_target g k hk) ((edge (k := 1) 0 1) q)
  have h₀ : StdSimplex.map spanChartFace.toOrderHom ((edge (k := 1) 0 1) q) =
      (edge (k := 7) 0 3) q := map_edge spanChartFace 0 1 q
  have h₁ : StdSimplex.map chartTerminalFace.toOrderHom ((edge (k := 1) 0 1) q) =
      (edge (k := 7) 6 7) q := map_edge chartTerminalFace 0 1 q
  exact (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.nodes g k hk)) h₀).symm.trans
      (h.trans (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartSquareParameter.nodes g k hk)) h₁))

/-- The complete positive seam keeps the original chart evaluation without a pause. -/
theorem plus (q : unitInterval) :
    InputSpanParameterWord.parameter g (q, 0) =
      InputChartSquareParameter.plusParameter g (q, 1) :=
  (parameter_left g q).trans (chart_left g
    AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.plus GlobalRawBass.plus_projection q)

/-- The inverse seam retains its distinct full chart and the same original comparison clock. -/
theorem minus (q : unitInterval) :
    InputSpanParameterWord.parameter g (q, 1) =
      InputChartSquareParameter.minusParameter g (q, 1) :=
  (parameter_right g q).trans (chart_left g
    AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.minus GlobalRawBass.minus_projection q)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSeams
