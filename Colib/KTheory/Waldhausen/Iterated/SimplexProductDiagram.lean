/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Realization.SimplexProductGrid
public import Colib.KTheory.Waldhausen.Iterated.SimplexDiagonalComposition

/-!
# The common-reference simplex of two composable parameter families

The model vertices are the literal composites. The ordered grid and all its
faces use the actual simplicial product. Adapted from
`Quillen/Waldhausen/SConstruction/Iterated/SimplexProductDiagram.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory Topology
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceProduct
open SmallWaldhausenCategory SSet

variable {V W T : WideSubcategory preservesZero.{u}} {p q : ℕ}
variable (F₀ : V ⟶ W) (F : Fin (p + 1) → (V ⟶ W))
  (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor)
variable (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
  (σ : ∀ i, G₀.hom.toFunctor ≅ (G i).hom.toFunctor)

/-- Actual composites of the original model functors, indexed by the full grid. -/
def vertices (i : Fin (SimplexGrid.dimension p q + 1)) : V ⟶ T :=
  F ((SimplexGrid.indexEquiv p q).symm i).1 ≫
    G ((SimplexGrid.indexEquiv p q).symm i).2

/-- The reference is the image of the literal pair of reference isomorphisms under composition. -/
def references (i : Fin (SimplexGrid.dimension p q + 1)) :
    (F₀ ≫ G₀).hom.toFunctor ≅ (vertices F G i).hom.toFunctor :=
  (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
    ((ρ ((SimplexGrid.indexEquiv p q).symm i).1).prod
      (σ ((SimplexGrid.indexEquiv p q).symm i).2))

/-- One actual simplex extends the composite grid using its canonical common reference. -/
def simplex : ModelSimplex V T (SimplexGrid.dimension p q) :=
  ModelSimplex.ofIsos (F₀ ≫ G₀) (vertices F G) (references F₀ F ρ G₀ G σ)

/-- Simultaneous monotone time paths in the two grids determine an original simplex face. -/
def gridFace {m : ℕ} (α : ⦋m⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    ⦋m⦌ ⟶ ⦋SimplexGrid.dimension p q⦌ :=
  SimplexCategory.Hom.mk ((SimplexGrid.index p q).comp
    (OrderHom.prod α.toOrderHom β.toOrderHom))

/-- Every whole grid chain is the literal diagonal composition of its two input chains. -/
theorem grid_face {m : ℕ} (α : ⦋m⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    (simplex F₀ F ρ G₀ G σ).face (gridFace α β) =
      ((ModelSimplex.ofIsos F₀ F ρ).face α).diagonalComposition
        ((ModelSimplex.ofIsos G₀ G σ).face β) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face,
    ModelSimplex.ofIsos_face, ModelSimplex.diagonalComposition_ofIsos]
  refine ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ ⟨vertices F G ((gridFace α β).toOrderHom i),
      references F₀ F ρ G₀ G σ ((gridFace α β).toOrderHom i)⟩)
    (fun i ↦ ⟨F (α.toOrderHom i) ≫ G (β.toOrderHom i),
      (Functor.uncurry.obj (whiskeringLeft V.obj.Obj W.obj.Obj T.obj.Obj)).mapIso
        ((ρ (α.toOrderHom i)).prod (σ (β.toOrderHom i)))⟩) ?_
  intro i
  change (⟨vertices F G (SimplexGrid.index p q (α.toOrderHom i, β.toOrderHom i)),
    references F₀ F ρ G₀ G σ (SimplexGrid.index p q (α.toOrderHom i, β.toOrderHom i))⟩ :
      Σ J : V ⟶ T, (F₀ ≫ G₀).hom.toFunctor ≅ J.hom.toFunctor) = _
  unfold vertices references
  rw [SimplexGrid.decode_index]

/-- Every original iterated S-level evaluates two independent simplicial parameters by composition.
The grid parameter does not identify either time with an S-construction or structure coordinate. -/
theorem stage_comp (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[p]).obj n) (θ : (Δ[q]).obj n) :
    stageSimplexFunction r (simplex F₀ F ρ G₀ G σ) n A
      ((SimplexGrid.embedding p q).app n (τ, θ)) =
      stageSimplexFunction r (ModelSimplex.ofIsos G₀ G σ) n
        (stageSimplexFunction r (ModelSimplex.ofIsos F₀ F ρ) n A τ) θ := by
  let α := τ.down
  let β := θ.down
  let e : (Δ[n.unop.len]).obj n := ⟨𝟙 n.unop⟩
  have hα : (⟨e.down ≫ α⟩ : (Δ[p]).obj n) = τ := by
    apply ULift.ext
    exact Category.id_comp _
  have hβ : (⟨e.down ≫ β⟩ : (Δ[q]).obj n) = θ := by
    apply ULift.ext
    exact Category.id_comp _
  calc
    _ = stageSimplexFunction r
        ((simplex F₀ F ρ G₀ G σ).face (gridFace α β)) n A e :=
      stageSimplexFunction_face r (simplex F₀ F ρ G₀ G σ) (gridFace α β) n A e
    _ = stageSimplexFunction r ((ModelSimplex.ofIsos G₀ G σ).face β) n
        (stageSimplexFunction r ((ModelSimplex.ofIsos F₀ F ρ).face α) n A e) e := by
      rw [grid_face, stageSimplexFunction_diagonalComposition]
    _ = _ := by
      rw [← stageSimplexFunction_face r (ModelSimplex.ofIsos F₀ F ρ) α n A e]
      rw [hα]
      simpa only [hβ] using
        (stageSimplexFunction_face r (ModelSimplex.ofIsos G₀ G σ) β n
          (stageSimplexFunction r (ModelSimplex.ofIsos F₀ F ρ) n A τ) e).symm

/-- The whole simplicial family keeps the actual product of its two independent parameters. -/
theorem stage_transformation_comp (r : ℕ) :
    (α_ ((stages r).obj V) Δ[p] Δ[q]).hom ≫
      ((stages r).obj V) ◁ SimplexGrid.embedding p q ≫
      stageTransformationSimplex r (simplex F₀ F ρ G₀ G σ) =
    (stageTransformationSimplex r (ModelSimplex.ofIsos F₀ F ρ)) ▷ Δ[q] ≫
      stageTransformationSimplex r (ModelSimplex.ofIsos G₀ G σ) := by
  ext n z : 4
  exact stage_comp F₀ F ρ G₀ G σ r n z.1.1 z.1.2 z.2

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceProduct
