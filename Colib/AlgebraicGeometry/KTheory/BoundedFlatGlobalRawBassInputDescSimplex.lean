/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionRectangleParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionReference

/-!
# Both original global raw input rectangles in their exact shared diagram

Only the five complete outer-projection nodes are shared. The original thirty-one-vertex
order and both full rectangle inclusions preserve every original scalar pasting parameter.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputDescSimplex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original raw Laurent total map is the common geometric reference. -/
abbrev reference :=
  BoundedFlatPerfectProjectionReference.reference (laurent.map g) (laurentProjection.app Y)

/-- Each geometric node retains its entire natural-isomorphism anchor. -/
abbrev Node := BoundedFlatPerfectProjectionReference.Node (laurent.map g) (laurentProjection.app Y)

/-- Every original chart rectangle is transported only by its actual projection equation. -/
def chartNodes (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z) : Fin 18 → Node g :=
  BoundedFlatPerfectProjectionReference.nodes (projection.app Y) (k.app Y)
    (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (k.naturality g) (laurentProjection.app Y) (hk Y)

/-- The actual two geometric chart diagrams share all five outer-track nodes. -/
theorem shared_nodes (i : Fin 5) :
    chartNodes g plus plus_projection (BoundedFlatPerfectProjectionReference.sharedIndex i) =
      chartNodes g minus minus_projection (BoundedFlatPerfectProjectionReference.sharedIndex i) :=
  BoundedFlatPerfectProjectionReference.two_projection_shared (projection.app Y) (plus.app Y)
    (projection.app X) (plus.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (plus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (plus_projection Y) (plus_projection X) (minus.app Y) (minus.app X)
    (minus.naturality g) (minus_projection Y) (minus_projection X) i

/-- The original shared order retains thirteen separate nodes for each Laurent chart. -/
def nodes (i : Fin 31) : Node g :=
  if h₀ : i.val < 14 then chartNodes g plus plus_projection ⟨i.val, by omega⟩ else
    if h₁ : i.val < 25 then chartNodes g minus minus_projection ⟨i.val - 11, by omega⟩ else
      if h₂ : i.val < 29 then chartNodes g plus plus_projection ⟨i.val - 11, by omega⟩ else
        chartNodes g minus minus_projection ⟨i.val - 13, by omega⟩

/-- The full original raw two-chart diagram is a genuine Model simplex. -/
def simplex : ModelSimplex (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn Y))
    (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn (laurent.obj X))) 30 :=
  ModelSimplex.ofIsos (reference g) (fun i => (nodes g i).1) (fun i => (nodes g i).2)

/-- Every positive chart node keeps its complete geometric anchor. -/
theorem plus_nodes (i : Fin 18) :
    nodes g (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom i) =
      chartNodes g plus plus_projection i := by
  fin_cases i <;> rfl

/-- Every inverse chart node keeps its anchor, including all five common outer nodes. -/
theorem minus_nodes (i : Fin 18) :
    nodes g (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom i) =
      chartNodes g minus minus_projection i := by
  fin_cases i
  · exact shared_nodes g 0
  · exact shared_nodes g 1
  · exact shared_nodes g 2
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact shared_nodes g 3
  · exact shared_nodes g 4
  · rfl
  · rfl

private theorem chart_simplex (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z) :
    ModelSimplex.ofIsos (reference g) (fun i => (chartNodes g k hk i).1)
      (fun i => (chartNodes g k hk i).2) =
    BoundedFlatPerfectDoubleSquareMergedSimplex.simplex (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g) :=
  BoundedFlatPerfectProjectionReference.simplex_original (projection.app Y) (k.app Y)
    (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (k.naturality g) (laurentProjection.app Y) (hk Y)

/-- The complete positive face is the unchanged original geometric rectangle. -/
theorem plus_face : (simplex g).face BoundedFlatCoefficientBassH0Diagram.plusFace =
    BoundedFlatPerfectDoubleSquareMergedSimplex.simplex (projection.app Y) (plus.app Y)
      (projection.app X) (plus.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (plus.naturality g) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (plus_nodes g)).trans
    (chart_simplex g plus plus_projection)

/-- The complete inverse face preserves its separate original geometric rectangle. -/
theorem minus_face : (simplex g).face BoundedFlatCoefficientBassH0Diagram.minusFace =
    BoundedFlatPerfectDoubleSquareMergedSimplex.simplex (projection.app Y) (minus.app Y)
      (projection.app X) (minus.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (minus.naturality g) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (minus_nodes g)).trans
    (chart_simplex g minus minus_projection)


end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputDescSimplex
