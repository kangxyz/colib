/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.WeakObjectSimplex
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectLoops
public import Colib.KTheory.Waldhausen.BisimplexRealization

/-! # The literal constant nerve direction of an identity weak-object square -/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/WeakObjectIdentitySquare.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory Convexity
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C) (A : C)

/-- The entire original identity weak square factors through its unchanged object edge. -/
theorem weakObjectIdentitySquare_family :
    bisimplexFamily W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property) =
      CartesianMonoidalCategory.fst Δ[1] Δ[1] ≫
        SSet.yonedaEquiv.symm (W.kZeroObjectSimplex A) := by
  have hK : ComposableArrows.mk₁ (W.oneWeakArrow (𝟙 A) (W.weq.id_mem A)) =
      (Functor.const (Fin 2)).obj (⟨(oneEmbedding W).obj A⟩ : WeakRows W ⦋1⦌) := by
    refine ComposableArrows.ext₁
      (F := ComposableArrows.mk₁ (W.oneWeakArrow (𝟙 A) (W.weq.id_mem A)))
      (G := (Functor.const (Fin 2)).obj (⟨(oneEmbedding W).obj A⟩ : WeakRows W ⦋1⦌))
      rfl rfl ?_
    simp [oneWeakArrow]
    rfl
  ext n z
  apply Subtype.ext
  change gridMap₂ z.1.down z.2.down ⋙
      weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow (𝟙 A) (W.weq.id_mem A))) =
    intervalProjection n.unop ⋙ indexMap z.1.down ⋙ oneDiagram W A
  rw [hK]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [Functor.comp_map, weakChainToGrid_map, Functor.const,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  change (oneDiagram W A).map _ ≫ 𝟙 _ = (oneDiagram W A).map _
  rw [Category.comp_id]
  rfl

/-- Every value is the actual original object loop, independently of the nerve parameter. -/
theorem weakObjectIdentitySquare_realization (s t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) =
      W.kZeroObjectLoop A t := by
  let p := (realizationProductSimplexHomeomorph.{max u v} 1 1).symm
    (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s)
  have hp := (realizationProductSimplexHomeomorph.{max u v} 1 1).apply_symm_apply
    (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s)
  have hp₁ : SSet.toTop.map (CartesianMonoidalCategory.fst Δ[1] Δ[1]) p =
      realizationInterval t := by
    apply (SimplexCategory.toTopHomeo ⦋1⦌).injective
    change SimplexCategory.toTopHomeo ⦋1⦌
      (SSet.toTop.map (CartesianMonoidalCategory.fst Δ[1] Δ[1]) p) =
        SimplexCategory.toTopHomeo ⦋1⦌
          ((SimplexCategory.toTopHomeo ⦋1⦌).symm (StdSimplex.homeomorphI.symm t))
    rw [Homeomorph.apply_symm_apply]
    exact congrArg _root_.Prod.fst hp
  rw [bisimplexRealization_apply, weakObjectIdentitySquare_family, Functor.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm (W.kZeroObjectSimplex A))
    (SSet.toTop.map (CartesianMonoidalCategory.fst Δ[1] Δ[1]) p) = _
  rw [hp₁]
  rfl

end CategoryTheory.Waldhausen.Structure
