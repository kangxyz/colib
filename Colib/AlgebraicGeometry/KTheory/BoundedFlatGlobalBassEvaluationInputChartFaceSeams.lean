/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartFaceNodes
public import Colib.KTheory.Waldhausen.Iterated.SimplexCollapsedEdges

/-!
# Complete evaluation edges of the original mixed descent faces

The original three-side collapse and attached commuting-square parameters agree on their
entire evaluation edges. These scalar identities use equality of the complete Model nodes
and their actual anchors, retaining the original unpaused evaluation clocks.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartFaceSeams
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem map_edge_scalar {p q : ℕ} (α : ⦋p⦌ ⟶ ⦋q⦌)
    (i j : Fin (p + 1)) (r : unitInterval) :
    StdSimplex.map α.toOrderHom ((edge i j) r) =
      (edge (α.toOrderHom i) (α.toOrderHom j)) r := map_edge α i j r

private def evaluationFace : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩

private def targetFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩

/-- The target evaluation edge is the full original postcomposed chart evaluation. -/
theorem post_edge (r : unitInterval) :
    InputChartSquareParameter.edge g k hk 3 4 r =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.postNode g k hk) ((edge 0 3) r) := by
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputChartReference.postNode g k hk) (InputChartSquareParameter.nodes g k hk)
    evaluationFace targetFace (fun i => by
      fin_cases i
      · exact InputChartFaceNodes.post_source_node g k hk
      · exact InputChartFaceNodes.post_target_node g k hk) ((edge (k := 1) 0 1) r)
  rw [map_edge_scalar, map_edge_scalar] at h
  simpa only [InputChartSquareParameter.edge, Path.map_coe,
    Function.comp_apply, targetFace, evaluationFace, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- The positive postcomposed boundary retains the whole original evaluation edge. -/
theorem post_plus (r : unitInterval) :
    InputMixedDesc.postSquareParameter g (r, 0) =
      InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 3 4 r := by
  change CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y)
      (collapsed InputChartSimplex.descParameter (r, 0))) = _
  rw [collapsed_left_path, post_edge]
  have h := InputChartReference.plus_post_parameter g ((edge 0 3) r)
  rw [map_edge_scalar] at h
  exact h.symm

/-- The inverse postcomposed boundary retains its distinct full original evaluation edge. -/
theorem post_minus (r : unitInterval) :
    InputMixedDesc.postSquareParameter g (r, 1) =
      InputChartSquareParameter.edge g minus GlobalRawBass.minus_projection 3 4 r := by
  change CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y)
      (collapsed InputChartSimplex.descParameter (r, 1))) = _
  rw [collapsed_right_path, post_edge]
  have h := InputChartReference.minus_post_parameter g ((edge 0 3) r)
  rw [map_edge_scalar] at h
  exact h.symm

private def sourceFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 6], by decide⟩

/-- The source evaluation edge is the entire original strict-precomposed chart evaluation. -/
theorem pre_edge (r : unitInterval) :
    InputChartSquareParameter.edge g k hk 0 6 r =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.preNode g k hk) ((edge 0 3) r) := by
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputChartReference.preNode g k hk) (InputChartSquareParameter.nodes g k hk)
    evaluationFace sourceFace (fun i => by
      fin_cases i
      · exact InputChartFaceNodes.pre_source_node g k hk
      · exact InputChartFaceNodes.pre_target_node g k hk) ((edge (k := 1) 0 1) r)
  rw [map_edge_scalar, map_edge_scalar] at h
  simpa only [InputChartSquareParameter.edge, Path.map_coe,
    Function.comp_apply, sourceFace, evaluationFace, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- The complete original positive source seam agrees in the actual common-reference nerve. -/
theorem pre_plus (r : unitInterval) :
    InputMixedDesc.preSquareParameter g (r, 0) =
      InputChartSquareParameter.parameter g plus GlobalRawBass.plus_projection (0, r) := by
  change CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
      (collapsed InputChartSimplex.descParameter (r, 0))) = _
  rw [collapsed_left_path, InputChartSquareParameter.parameter_zero, pre_edge]
  have h := InputChartReference.plus_pre_parameter g ((edge 0 3) r)
  rw [map_edge_scalar] at h
  exact h.symm

/-- The inverse source seam keeps its own full original X-chart evaluation and strict transport. -/
theorem pre_minus (r : unitInterval) :
    InputMixedDesc.preSquareParameter g (r, 1) =
      InputChartSquareParameter.parameter g minus GlobalRawBass.minus_projection (0, r) := by
  change CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
      (collapsed InputChartSimplex.descParameter (r, 1))) = _
  rw [collapsed_right_path, InputChartSquareParameter.parameter_zero, pre_edge]
  have h := InputChartReference.minus_pre_parameter g ((edge 0 3) r)
  rw [map_edge_scalar] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartFaceSeams
