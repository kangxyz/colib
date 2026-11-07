/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectCompositionRealization
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectIdentitySquare

/-!
# The original square-parametrized weak-object track

This track uses the whole original weak-arrow square with independent nerve and object-loop
times. Its literal faces identify both object loops. It is the specified fine projection track
used together with the original cofiber triangle, rather than a choice of a homotopy witness.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/WeakObjectSquareTrack.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Also `GrothendieckComparison/WeakObjectCompositionTrack.lean`, lines 28–35 only.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B : C} (f : A ⟶ B) (hf : W.weq f)

/-- The constant initial nerve face is the original identity square of the source. -/
theorem weakObjectSquare_initial_grid :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0) ⋙
        (W.weakObjectSimplex f hf).val =
      (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val := by
  change gridMap₂ _ _ ⋙ weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)) =
    weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow (𝟙 A) (W.weq.id_mem A)))
  rw [weakChainToGrid_precomp_nerve]
  congr 1
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp [oneWeakArrow, SimplexCategory.const, Monotone.functor]
  rfl

/-- The constant terminal nerve face is the original identity square of the target. -/
theorem weakObjectSquare_terminal_grid :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1) ⋙
        (W.weakObjectSimplex f hf).val =
      (W.weakObjectSimplex (𝟙 B) (W.weq.id_mem B)).val := by
  change gridMap₂ _ _ ⋙ weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)) =
    weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow (𝟙 B) (W.weq.id_mem B)))
  rw [weakChainToGrid_precomp_nerve]
  congr 1
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp [oneWeakArrow, SimplexCategory.const, Monotone.functor]
  rfl

/-- The initial nerve endpoint is the original A object loop, at every loop time. -/
theorem weakObjectSquare_initial (t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm 0) =
      W.kZeroObjectLoop A t := by
  have h := bisimplexRealization_precomp W (W.weakObjectSimplex f hf).val
    ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
    (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)
    (StdSimplex.homeomorphI.symm t) (StdSimplex.homeomorphI.symm 0)
  have he := bisimplexRealization_congr W _
    (((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property).precomp
      W.cof W.weq (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0))
    ((isSimplex₂_diagonal_iff _ _ _).mpr
      (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
    (W.weakObjectSquare_initial_grid f hf)
  rw [he] at h
  have hc : (ConcreteCategory.hom (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) 0 = 0 := rfl
  have hi : (⇑(ConcreteCategory.hom (𝟙 ⦋1⦌)) : Fin 2 → Fin 2) = id := rfl
  have hh := h.trans (W.weakObjectIdentitySquare_realization A 0 t)
  simpa only [StdSimplex.homeomorphI_symm_zero, StdSimplex.homeomorphI_symm_one,
    StdSimplex.map_single, hc, hi, StdSimplex.map_id] using hh

/-- The terminal nerve endpoint is the original B object loop, at every loop time. -/
theorem weakObjectSquare_terminal (t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm 1) =
      W.kZeroObjectLoop B t := by
  have h := bisimplexRealization_precomp W (W.weakObjectSimplex f hf).val
    ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
    (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)
    (StdSimplex.homeomorphI.symm t) (StdSimplex.homeomorphI.symm 0)
  have he := bisimplexRealization_congr W _
    (((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property).precomp
      W.cof W.weq (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1))
    ((isSimplex₂_diagonal_iff _ _ _).mpr
      (W.weakObjectSimplex (𝟙 B) (W.weq.id_mem B)).property)
    (W.weakObjectSquare_terminal_grid f hf)
  rw [he] at h
  have hc : (ConcreteCategory.hom (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) 0 = 1 := rfl
  have hi : (⇑(ConcreteCategory.hom (𝟙 ⦋1⦌)) : Fin 2 → Fin 2) = id := rfl
  have hh := h.trans (W.weakObjectIdentitySquare_realization B 0 t)
  simpa only [StdSimplex.homeomorphI_symm_zero, StdSimplex.homeomorphI_symm_one,
    StdSimplex.map_single, hc, hi, StdSimplex.map_id] using hh

/-- Both entire object-edge endpoint lines are the literal chosen basepoint. -/
theorem weakObjectSquare_vertex (e : Fin 2) (s : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.single e, StdSimplex.homeomorphI.symm s) = W.kBasepoint := by
  have he := W.weakObjectCompositionRealization_first f (𝟙 B) hf (W.weq.id_mem B)
    (StdSimplex.single e) (StdSimplex.homeomorphI.symm s)
  exact he.symm.trans (W.weakObjectCompositionRealization_vertex f (𝟙 B) hf (W.weq.id_mem B)
    e ((StdSimplex.homeomorphI.symm s).map (SimplexCategory.δ 2)))

/-- The actual weak-arrow square is a specified endpoint-relative object-loop homotopy. -/
def weakObjectSquareTrack : (W.kZeroObjectLoop A).Homotopy (W.kZeroObjectLoop B) where
  toFun z := bisimplexRealization W (W.weakObjectSimplex f hf).val
    ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
    (StdSimplex.homeomorphI.symm z.2, StdSimplex.homeomorphI.symm z.1)
  continuous_toFun := by fun_prop
  map_zero_left := W.weakObjectSquare_initial f hf
  map_one_left := W.weakObjectSquare_terminal f hf
  prop' s t ht := by
    rcases ht with rfl | rfl
    · change bisimplexRealization W _ _ (StdSimplex.homeomorphI.symm 0, _) = _
      rw [StdSimplex.homeomorphI_symm_zero, W.weakObjectSquare_vertex f hf]
      exact (W.kZeroObjectLoop A).source.symm
    · change bisimplexRealization W _ _ (StdSimplex.homeomorphI.symm 1, _) = _
      rw [StdSimplex.homeomorphI_symm_one, W.weakObjectSquare_vertex f hf]
      exact (W.kZeroObjectLoop A).target.symm

/-- The full square track retains the original nerve and object-loop parameters. -/
theorem weakObjectSquareTrack_apply (s t : unitInterval) :
    W.weakObjectSquareTrack f hf (s, t) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) := rfl

/-- Curry the entire original weak-arrow square into its specified path of based loops. -/
def weakObjectSquareLoopPath : Path (W.kZeroObjectLoop A) (W.kZeroObjectLoop B) where
  toFun s := (W.weakObjectSquareTrack f hf).eval s
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.weakObjectSquareTrack f hf).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

end CategoryTheory.Waldhausen.Structure

/-!
## Additional implementation provenance

Adapted from `Quillen/Waldhausen/AutomorphismKOne.lean`, lines 43–50 and 87–92,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original declarations, full coordinates, hypotheses and universes are retained.
Only native namespaces, precise imports and line wrapping change. Source-only, UNCOMPILED.
-/
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The identity weak-arrow loop is the literal constant path at the object loop. -/
theorem weakObjectSquareLoopPath_id (A : C) :
    W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A) = Path.refl (W.kZeroObjectLoop A) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact W.weakObjectIdentitySquare_realization A s t

/-- The original square path respects equality of its arrow, independently of its certificate. -/
theorem weakObjectSquareLoopPath_congr {A B : C} {f g : A ⟶ B}
    (h : f = g) (hf : W.weq f) (hg : W.weq g) :
    W.weakObjectSquareLoopPath f hf = W.weakObjectSquareLoopPath g hg := by
  subst g
  rfl

end CategoryTheory.Waldhausen.Structure
