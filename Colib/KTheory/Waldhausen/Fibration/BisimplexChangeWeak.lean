/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.Fibration.BisimplexChangeWeak
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.KTheory.Waldhausen.BisimplexRealization

/-! # Original change of weakness on entire bisimplex families

The original localization map retains the full fine grid and both realization coordinates.
This is the precise comparison used for the fine weak projection of a scalar factorization.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/BisimplexChangeWeak.lean`
lines 38–47 and 64–78 at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The same grid, both certificates and independent barycentric coordinates are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity MonoidalCategory SSet
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {n m : ℕ}
  (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ V.cof V.weq F)
  (hG : IsSimplex₂ N.coarse.cof N.coarse.weq F)

/-- Both original barycentric coordinates survive the actual localization map. -/
theorem bisimplexRealization_changeWeak
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    changeWeakMap N (bisimplexRealization V F hF (z, t)) =
      bisimplexRealization N.coarse F hG (z, t) := by
  change (SSet.toTop.map (bisimplexFamily V F hF) ≫
    SSet.toTop.map (sSetMap (changeWeak_exact N)))
      ((realizationProductSimplexHomeomorph n m).symm (z, t)) = _
  rw [← Functor.map_comp, bisimplexFamily_changeWeak N F hF hG]
  rfl

/-- The entire fine weak-arrow square is retained through the original localization map. -/
theorem weakObjectSquare_changeWeak {A B : C} (f : A ⟶ B) (hf : V.weq f)
    (t z : StdSimplex ℝ (Fin 2)) :
    changeWeakMap N (bisimplexRealization V (V.weakObjectSimplex f hf).val
      ((isSimplex₂_diagonal_iff _ _ _).mpr (V.weakObjectSimplex f hf).property) (t, z)) =
      bisimplexRealization N.coarse (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).property) (t, z) := by
  have he := weakObjectSimplex_val_of_zero_eq N.coarse N.zero_eq.symm f hf (N.le_weq _ hf)
  have hc : IsSimplex₂ N.coarse.cof N.coarse.weq (V.weakObjectSimplex f hf).val := by
    rw [he]
    exact (isSimplex₂_diagonal_iff _ _ _).mpr
      (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).property
  rw [bisimplexRealization_changeWeak N _ _ hc]
  exact DFunLike.congr_fun (bisimplexRealization_congr N.coarse _ hc _ he) (t, z)

attribute [colib_tag "COL-0299"] bisimplexRealization_changeWeak

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/BisimplexChangeWeak.lean:39-47" "adaptation"
  "The original changeWeak map preserves the same entire bisimplex with both certificates,
    arbitrary independent degrees and both barycentric coordinates"]
  bisimplexRealization_changeWeak

attribute [colib_tag "COL-0299"] weakObjectSquare_changeWeak

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/BisimplexChangeWeak.lean:65-78" "adaptation"
  "The entire fine weak-arrow square maps to the coarse square of the same arrow with its
    actual fine-to-coarse weakness certificate and independent coordinates"]
  weakObjectSquare_changeWeak

end CategoryTheory.Waldhausen.Fibration
