/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterWord
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterEdges
public import Colib.KTheory.Waldhausen.Iterated.SimplexCollapsedEdges

/-!
# The complete source seam of the original input-span parameter

Full finite projection nodes and the unchanged first normalization rows identify the source
word before evaluation. Every original half and quarter coordinate is retained.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSource
open GlobalSectionChangeIndex InputSpanParameterWord
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The original simplex edge formula in its literal parameter-map form. -/
theorem map_edge_raw {l m : ℕ} (α : ⦋l⦌ ⟶ ⦋m⦌) (i j : Fin (l + 1))
    (s : unitInterval) :
    StdSimplex.map α.toOrderHom (edge i j s) = edge (α.toOrderHom i) (α.toOrderHom j) s :=
  map_edge α i j s

private def projectionSourceFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 6], by decide⟩

private def preSourceFace : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩

/-- The entire projection source edge is the actual strict-precomposed evaluation cut. -/
theorem projection_source (s : unitInterval) :
    chartSwap g k hk (s, 0) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.preNode g k hk) ((edge 3 4) s) := by
  change CommonReferenceNerve.parameter _ _ (InputCommutingParameter.parameter (0, s)) = _
  rw [InputCommutingParameter.parameter_zero]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputChartReference.preNode g k hk) (InputSpanParameterNodes.nodes g k hk)
    preSourceFace projectionSourceFace (fun i => by
      fin_cases i
      · exact InputSpanParameterEdges.projection_pre_source g k hk
      · exact (InputSpanParameterNodes.node_six g k hk).trans
          (InputChartReference.prism_pre_nodes g k hk 2)) ((edge (k := 1) 0 1) s)
  have h₀ : StdSimplex.map projectionSourceFace.toOrderHom ((edge (k := 1) 0 1) s) =
      (edge (k := 7) 0 6) s := map_edge projectionSourceFace 0 1 s
  have h₁ : StdSimplex.map preSourceFace.toOrderHom ((edge (k := 1) 0 1) s) =
      (edge (k := 4) 3 4) s := map_edge preSourceFace 0 1 s
  exact (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.nodes g k hk)) h₀).symm.trans
      (h.trans (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.preNode g k hk)) h₁))

/-- The original split normalization path in the five-node chart. -/
def normalizationPath := (edge (k := 4) 1 2).trans (edge 2 4)

private theorem normalization_map {l : ℕ} (α : ⦋4⦌ ⟶ ⦋l⦌) (s : unitInterval) :
    StdSimplex.map α.toOrderHom (normalizationPath s) =
      ((edge (α.toOrderHom 1) (α.toOrderHom 2)).trans
        (edge (α.toOrderHom 2) (α.toOrderHom 4))) s := by
  change StdSimplex.map α.toOrderHom (((edge 1 2).trans (edge 2 4)) s) = _
  rw [Path.trans_apply, Path.trans_apply]
  split <;> exact map_edge α _ _ _

/-- The whole first prism row is the original split strict-precomposed normalization. -/
theorem normalization_source (s : unitInterval) :
    normalizationSwap g k hk (s, 0) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputChartReference.preNode g k hk) (normalizationPath s) := by
  change InputSpanParameterPrism.parameter g k hk (0, s) = _
  rw [InputSpanParameterPrism.parameter_eq]
  rw [show (edge (k := 1) 0 1) 0 = StdSimplex.single 0 from (edge 0 1).source]
  have hp := InputChartReference.prism_pre_parameter g k hk
    (InputSpanParameterPrism.splitPath s)
  rw [SimplexGrid.parameter_row] at hp ⊢
  refine hp.trans (congrArg
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.preNode g k hk)) ?_)
  have he : InputParameter.reindexPath
      (InputSimplex.triangleFace 1 2 4 (by decide) (by decide))
      InputSpanParameterPrism.splitPath = normalizationPath := by
    change InputParameter.reindexPath _ ((edge 0 1).trans (edge 1 2)) = _
    simp only [InputParameter.reindexPath_trans, InputParameter.reindexPath_edge]
    rfl
  exact DFunLike.congr_fun he s

/-- The actual attached characteristic map of the original complete X descent diagram. -/
def sourceCharacteristic :=
  (CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)).comp
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X))

private theorem plus_projection (s : unitInterval) :
    chartSwap g plus GlobalRawBass.plus_projection (s, 0) =
      sourceCharacteristic g ((edge (k := 7) 3 4) s) := by
  rw [projection_source]
  have h := InputChartReference.plus_pre_parameter g ((edge 3 4) s)
  have he : StdSimplex.map InputChartSimplex.plusFace.toOrderHom ((edge (k := 4) 3 4) s) =
      (edge (k := 7) 3 4) s := map_edge InputChartSimplex.plusFace 3 4 s
  exact h.trans (congrArg (sourceCharacteristic g) he)

private theorem minus_projection (s : unitInterval) :
    chartSwap g minus GlobalRawBass.minus_projection (s, 0) =
      sourceCharacteristic g ((edge (k := 7) 6 7) s) := by
  rw [projection_source]
  have h := InputChartReference.minus_pre_parameter g ((edge 3 4) s)
  have he : StdSimplex.map InputChartSimplex.minusFace.toOrderHom ((edge (k := 4) 3 4) s) =
      (edge (k := 7) 6 7) s := map_edge InputChartSimplex.minusFace 3 4 s
  exact h.trans (congrArg (sourceCharacteristic g) he)

private theorem plus_normalization (s : unitInterval) :
    normalizationSwap g plus GlobalRawBass.plus_projection (s, 0) =
      sourceCharacteristic g (((edge (k := 7) 1 2).trans (edge 2 4)) s) := by
  rw [normalization_source]
  have h := InputChartReference.plus_pre_parameter g (normalizationPath s)
  rw [normalization_map] at h
  exact h

private theorem minus_normalization (s : unitInterval) :
    normalizationSwap g minus GlobalRawBass.minus_projection (s, 0) =
      sourceCharacteristic g (((edge (k := 7) 1 5).trans (edge 5 7)) s) := by
  rw [normalization_source]
  have h := InputChartReference.minus_pre_parameter g (normalizationPath s)
  rw [normalization_map] at h
  exact h

private theorem overlap_source (s : unitInterval) :
    overlapSwap g (s, 0) = sourceCharacteristic g
      (((((edge (k := 7) 1 2).trans (edge 2 4)).symm).trans
        ((edge 1 5).trans (edge 5 7))) s) := by
  unfold overlapSwap
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact plus_normalization g (unitInterval.symm _)
  · exact minus_normalization g _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSource

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSeams
open InputSpanParameterWord InputSpanParameterSource
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The whole source face ends at the exact source word of the actual input-span square. -/
theorem source (s : unitInterval) :
    InputMixedDesc.preSquareParameter g (1, s) = InputSpanParameterWord.parameter g (0, s) := by
  rw [InputSpanParameterWord.parameter_zero]
  change sourceCharacteristic g (collapsed InputChartSimplex.descParameter (1, s)) =
    movingSwap g (s, 0)
  rw [collapsed_top_path]
  change sourceCharacteristic g (((edge (k := 7) 3 4).trans
    (((((edge 1 2).trans (edge 2 4)).symm).trans ((edge 1 5).trans (edge 5 7))).trans
      (edge 6 7).symm)) s) =
    ((chartSwap g plus GlobalRawBass.plus_projection).trans
      ((overlapSwap g).trans (chartSwap g minus GlobalRawBass.minus_projection).symm)) (s, 0)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact (plus_projection g _).symm
  · rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split
    · exact (overlap_source g _).symm
    · exact (minus_projection g (unitInterval.symm _)).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSeams
