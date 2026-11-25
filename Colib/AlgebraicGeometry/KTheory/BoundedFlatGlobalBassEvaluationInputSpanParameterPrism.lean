/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputParameter
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartPreAttachment
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanSharedNodes

/-!
# The exact split-normalization faces of the original evaluation prisms

The terminal normalization face retains the original two-half raw composition track at the
moving evaluation input. Its terminal column is the entire evaluation side of the attached
projection square. Both charts share their complete initial column before evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace Topology
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterPrism
open GlobalSectionChangeIndex SmallWaldhausenCategory
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The original two-half normalization path, with its geometric intermediate retained. -/
def splitPath := (TheoremB.triangleEdgePath 0 1).trans
  (TheoremB.triangleEdgePath 1 2)

/-- Restrict only normalization comparison time, retaining both independent original times. -/
def parameter := (InputChartReference.prismParameter g k hk).comp
  (⟨fun z : unitInterval × unitInterval => (z.1, (1, z.2)), by fun_prop⟩ :
    C(unitInterval × unitInterval, unitInterval × (unitInterval × unitInterval)))

/-- The whole parameter is the original product with the actual split path. -/
theorem parameter_eq (r s : unitInterval) :
    parameter g k hk (r, s) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.prismNode g k hk)
      (SimplexGrid.parameter.{u+1} 1 2 ((edge (k := 1) 0 1) r, splitPath s)) := by
  change CommonReferenceNerve.parameter _ _
    (InputNormalizationPrism.parameter.{u+1} (r, (1, s))) = _
  rw [InputNormalizationPrism.parameter_normalization_one, splitPath]

/-- Every original normalization column retains the independent input evaluation edge. -/
def column (j : Fin 3) : C(unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  ⟨fun r => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.prismNode g k hk)
      (SimplexGrid.parameter.{u+1} 1 2
        ((edge (k := 1) 0 1) r, StdSimplex.single j)), by fun_prop⟩

/-- The whole common-source side is the unchanged initial normalization column. -/
theorem parameter_left (r : unitInterval) :
    parameter g k hk (r, 0) = column g k hk 0 r := by
  rw [parameter_eq]
  change _ = CommonReferenceNerve.parameter _ _ _
  rw [show splitPath 0 = StdSimplex.single 0 from splitPath.source]

/-- The whole target side is the unchanged terminal normalization column. -/
theorem parameter_right (r : unitInterval) :
    parameter g k hk (r, 1) = column g k hk 2 r := by
  rw [parameter_eq]
  change _ = CommonReferenceNerve.parameter _ _ _
  rw [show splitPath 1 = StdSimplex.single 2 from splitPath.target]

/-- The whole first row has the same actual total node for every valid chart factorization. -/
theorem shared_zero_node (l : laurent ⟶ polynomial)
    (hl : ∀ Z, l.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) :
    InputChartReference.prismNode g k hk 0 = InputChartReference.prismNode g l hl 0 := by
  calc
    _ = InputChartReference.preNode g k hk 1 :=
      InputChartReference.prism_pre_nodes g k hk 0
    _ = InputMixedDesc.preNode g (InputChartSimplex.chartNodes X (k.app X) (hk X) 1) :=
      InputChartReference.pre_nodes g k hk 1
    _ = InputMixedDesc.preNode g (InputChartSimplex.chartNodes X (l.app X) (hl X) 1) := by
      rw [InputChartSimplex.chartNodes_one, InputChartSimplex.chartNodes_one]
    _ = InputChartReference.preNode g l hl 1 :=
      (InputChartReference.pre_nodes g l hl 1).symm
    _ = _ := (InputChartReference.prism_pre_nodes g l hl 0).symm

/-- The converted total node is shared with its complete original raw rectangle anchor. -/
theorem shared_one_node (l : laurent ⟶ polynomial)
    (hl : ∀ Z, l.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z) :
    InputChartReference.prismNode g k hk 3 = InputChartReference.prismNode g l hl 3 := by
  exact (InputChartReference.prism_raw_nodes g k hk 0).trans
    ((InputSpanSharedNodes.shared_nodes g k hk l hl 4).trans
      (InputChartReference.prism_raw_nodes g l hl 0).symm)

/-- Both complete initial columns coincide before evaluating any native input. -/
theorem shared_column (l : laurent ⟶ polynomial)
    (hl : ∀ Z, l.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (r : unitInterval) : column g k hk 0 r = column g l hl 0 r := by
  change CommonReferenceNerve.parameter _ _ _ = CommonReferenceNerve.parameter _ _ _
  rw [SimplexGrid.parameter_column]
  apply CommonReferenceNerve.parameter_eq_of_face_nodes
  intro i
  fin_cases i
  · exact shared_zero_node g k hk l hl
  · exact shared_one_node g k hk l hl

/-- The local projection square uses exactly the two full nodes of the terminal prism column. -/
def projectionFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![6, 7], by decide⟩

/-- Every point of the projection evaluation side is the original terminal prism column. -/
theorem projection_column (r : unitInterval) :
    InputSpanParameterNodes.parameter g k hk (r, 1) = column g k hk 2 r := by
  change CommonReferenceNerve.parameter _ _ (InputCommutingParameter.parameter (r, 1)) = _
  rw [InputCommutingParameter.parameter_right]
  change CommonReferenceNerve.parameter _ _ _ = CommonReferenceNerve.parameter _ _ _
  rw [SimplexGrid.parameter_column]
  have he := DFunLike.congr_fun
    (InputParameter.reindexPath_edge (i := 0) (j := 1) projectionFace) r
  change StdSimplex.map projectionFace.toOrderHom ((edge (k := 1) 0 1) r) = edge 6 7 r at he
  rw [← he]
  apply CommonReferenceNerve.parameter_eq_of_face_nodes
  intro i
  fin_cases i
  · exact InputSpanParameterNodes.node_six g k hk
  · exact InputSpanParameterNodes.node_seven g k hk

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterPrism
