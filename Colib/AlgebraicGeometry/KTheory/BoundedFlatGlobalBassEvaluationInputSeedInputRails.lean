/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputUnitNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNull

/-! All four original whole carrier rails of the actual strict-unit times evaluation product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputRails
open CommonReferenceNerve InputSeedInputUnitProduct InputSeedInputUnitNodes
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem map_edge_scalar {p q : ℕ} (a : ⦋p⦌ ⟶ ⦋q⦌)
    (i j : Fin (p + 1)) (t : unitInterval) :
    StdSimplex.map a.toOrderHom ((edge i j) t) =
      edge (a.toOrderHom i) (a.toOrderHom j) t := map_edge a i j t

private theorem rail (a : ⦋1⦌ ⟶ ⦋3⦌) (b : ⦋1⦌ ⟶ ⦋15⦌)
    (h : ∀ i, nodes g (a.toOrderHom i) = InputSeedUnitNodes.nodes g (b.toOrderHom i))
    (t : unitInterval) :
    CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
        (StdSimplex.map a.toOrderHom ((edge (k := 1) 0 1) t)) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        (StdSimplex.map b.toOrderHom ((edge (k := 1) 0 1) t)) :=
  (parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g) (nodes g)
    (InputSeedUnitNodes.nodes g) a b (fun i ↦ (h i).symm) ((edge (k := 1) 0 1) t)).symm

private def sourceFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 8], by decide⟩

/-- The entire source rail retains both original full references and the unchanged time. -/
theorem source (t : unitInterval) :
    InputSeedInputUnitProduct.parameter g (0, t) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 0 8) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) t, (edge (k := 1) 0 1) 0))) = _
  rw [Path.source, Topology.SimplexGrid.parameter_column]
  have h := rail g (Topology.SimplexGrid.columnFace 1 1 0) sourceFace
    (fun i ↦ by
      fin_cases i
      · exact zero_node g
      · exact two_node g) t
  have he : StdSimplex.map sourceFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 0 8) t := map_edge_scalar sourceFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def targetFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![3, 11], by decide⟩

/-- The entire target rail retains both original full references and the unchanged time. -/
theorem target (t : unitInterval) :
    InputSeedInputUnitProduct.parameter g (1, t) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 3 11) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) t, (edge (k := 1) 0 1) 1))) = _
  rw [Path.target, Topology.SimplexGrid.parameter_column]
  have h := rail g (Topology.SimplexGrid.columnFace 1 1 1) targetFace
    (fun i ↦ by
      fin_cases i
      · exact one_node g
      · exact three_node g) t
  have he : StdSimplex.map targetFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 3 11) t := map_edge_scalar targetFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def bottomFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩

/-- The entire bottom rail retains both original full references and the unchanged time. -/
theorem bottom (t : unitInterval) :
    InputSeedInputUnitProduct.parameter g (t, 0) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 0 3) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) 0, (edge (k := 1) 0 1) t))) = _
  rw [Path.source, Topology.SimplexGrid.parameter_row]
  have h := rail g (Topology.SimplexGrid.rowFace 1 1 0) bottomFace
    (fun i ↦ by
      fin_cases i
      · exact zero_node g
      · exact one_node g) t
  have he : StdSimplex.map bottomFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 0 3) t := map_edge_scalar bottomFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def topFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![8, 11], by decide⟩

/-- The entire top rail retains both original full references and the unchanged time. -/
theorem top (t : unitInterval) :
    InputSeedInputUnitProduct.parameter g (t, 1) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 8 11) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) 1, (edge (k := 1) 0 1) t))) = _
  rw [Path.target, Topology.SimplexGrid.parameter_row]
  have h := rail g (Topology.SimplexGrid.rowFace 1 1 1) topFace
    (fun i ↦ by
      fin_cases i
      · exact two_node g
      · exact three_node g) t
  have he : StdSimplex.map topFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 8 11) t := map_edge_scalar topFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def chartFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩

/-- The full ordinary product rail is the original chart evaluation edge before inclusion. -/
theorem bottom_chart (r : I) : InputSeedInputUnitProduct.parameter g (r, 0) =
    InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 0 3 r := by
  rw [bottom]
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)
    (InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection)
    bottomFace chartFace (fun i ↦ by
      fin_cases i
      · exact InputLaurentSeams.source_node g plus GlobalRawBass.plus_projection
      · exact InputLaurentSeams.cut_node g plus GlobalRawBass.plus_projection)
    ((edge (k := 1) 0 1) r)
  exact (congrArg (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)) (map_edge_scalar bottomFace 0 1 r)).symm.trans
      (h.symm.trans (congrArg (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
        (InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection))
        (map_edge_scalar chartFace 0 1 r)))

/-- The full upper product rail is the actual unit-shifted chart edge before evaluation. -/
theorem top_chart (r : I) : InputSeedInputUnitProduct.parameter g (r, 1) =
    mapParameter (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
      (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 0 3 r) := by
  rw [top]
  change _ = mapParameter _ (CommonReferenceNerve.parameter _ _ ((edge (k := 7) 0 3) r))
  rw [mapParameter_parameter]
  have h := parameter_eq_of_face_nodes (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)
    (fun i ↦ ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
      (InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection i))
    topFace chartFace (fun i ↦ by
      fin_cases i
      · exact congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
          (InputLaurentSeams.source_node g plus GlobalRawBass.plus_projection)
      · exact congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
          (InputLaurentSeams.cut_node g plus GlobalRawBass.plus_projection))
    ((edge (k := 1) 0 1) r)
  exact (congrArg (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
    (InputSeedUnitNodes.nodes g)) (map_edge_scalar topFace 0 1 r)).symm.trans
      (h.symm.trans (congrArg (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
        (fun i ↦ ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
          (InputChartSquareParameter.nodes g plus GlobalRawBass.plus_projection i)))
        (map_edge_scalar chartFace 0 1 r)))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputRails
