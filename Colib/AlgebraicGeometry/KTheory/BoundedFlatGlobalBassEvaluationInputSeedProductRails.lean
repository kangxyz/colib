/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedProductSeams

/-! All four original whole carrier rails of the actual evaluation-times-unit product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedProductRails
open CommonReferenceNerve InputSeedEvaluationProduct InputSeedProductSeams
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
  SimplexCategory.Hom.mk ⟨![6, 14], by decide⟩

/-- The entire source rail retains both original full references and the unchanged time. -/
theorem source (t : unitInterval) :
    InputSeedEvaluationProduct.parameter g (0, t) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 6 14) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) 0, (edge (k := 1) 0 1) t))) = _
  rw [Path.source, Topology.SimplexGrid.parameter_row.{u + 1}]
  have h := rail g (Topology.SimplexGrid.rowFace 1 1 0) sourceFace
    (fun i ↦ by
      fin_cases i
      · exact zero_node g
      · exact one_node g) t
  have he : StdSimplex.map sourceFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 6 14) t := map_edge_scalar sourceFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def targetFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![7, 15], by decide⟩

/-- The entire target rail retains both original full references and the unchanged time. -/
theorem target (t : unitInterval) :
    InputSeedEvaluationProduct.parameter g (1, t) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 7 15) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) 1, (edge (k := 1) 0 1) t))) = _
  rw [Path.target, Topology.SimplexGrid.parameter_row.{u + 1}]
  have h := rail g (Topology.SimplexGrid.rowFace 1 1 1) targetFace
    (fun i ↦ by
      fin_cases i
      · exact two_node g
      · exact three_node g) t
  have he : StdSimplex.map targetFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 7 15) t := map_edge_scalar targetFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def bottomFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![6, 7], by decide⟩

/-- The entire bottom rail retains both original full references and the unchanged time. -/
theorem bottom (t : unitInterval) :
    InputSeedEvaluationProduct.parameter g (t, 0) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 6 7) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) t, (edge (k := 1) 0 1) 0))) = _
  rw [Path.source, Topology.SimplexGrid.parameter_column.{u + 1}]
  have h := rail g (Topology.SimplexGrid.columnFace 1 1 0) bottomFace
    (fun i ↦ by
      fin_cases i
      · exact zero_node g
      · exact two_node g) t
  have he : StdSimplex.map bottomFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 6 7) t := map_edge_scalar bottomFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

private def topFace : ⦋1⦌ ⟶ ⦋15⦌ :=
  SimplexCategory.Hom.mk ⟨![14, 15], by decide⟩

/-- The entire top rail retains both original full references and the unchanged time. -/
theorem top (t : unitInterval) :
    InputSeedEvaluationProduct.parameter g (t, 1) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (InputSeedUnitNodes.nodes g)
        ((edge (k := 15) 14 15) t) := by
  change CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)
    (Topology.SimplexGrid.parameter.{u + 1} 1 1
      (((edge (k := 1) 0 1) t, (edge (k := 1) 0 1) 1))) = _
  rw [Path.target, Topology.SimplexGrid.parameter_column.{u + 1}]
  have h := rail g (Topology.SimplexGrid.columnFace 1 1 1) topFace
    (fun i ↦ by
      fin_cases i
      · exact one_node g
      · exact three_node g) t
  have he : StdSimplex.map topFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 15) 14 15) t := map_edge_scalar topFace 0 1 t
  exact h.trans (congrArg
    (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
      (InputSeedUnitNodes.nodes g)) he)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedProductRails
