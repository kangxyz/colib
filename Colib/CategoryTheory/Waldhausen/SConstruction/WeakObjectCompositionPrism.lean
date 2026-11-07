/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.NerveReindex
public import Colib.CategoryTheory.Waldhausen.Rows.WeakObjectSimplex
public import Colib.CategoryTheory.Waldhausen.SConstruction.BisimplexFamily
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic


/-! # The first edge and constant vertex triangles of a weak composition

The original two weak arrows give their genuine weak-row nerve triangle. Its first
edge is the entire first weak-arrow square. Both vertex triangles are the literal
constant chosen-zero simplex; no continuous composition cube is assumed. -/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionPrism.lean`
   at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
   The constant-vertex theorem is from lines 24–46 of
   `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionBased.lean`
   at the same commit. Original maps, hypotheses and universes are retained.
   Source-only preparation; native validation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- The original weak-row chain on the genuine two-simplex. -/
def weakObjectCompositionPrism : Grid₂ ⦋1⦌ ⦋2⦌ ⥤ C :=
  weakChainToGrid W (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg))

/-- Every original quotient row and every original weak nerve arrow remains certified. -/
theorem weakObjectCompositionPrism_isSimplex₂ :
    IsSimplex₂ W.cof W.weq (W.weakObjectCompositionPrism f g hf hg) :=
  weakChainToGrid_isSimplex₂ W _

/-- The first nerve edge is the entire original first weak-arrow square. -/
theorem weakObjectCompositionPrism_first :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 2) ⋙ W.weakObjectCompositionPrism f g hf hg =
      (W.weakObjectSimplex f hf).val := by
  rw [weakObjectCompositionPrism, weakChainToGrid_precomp_nerve]
  change weakChainToGrid W ((nerve (WeakRows W ⦋1⦌)).δ 2
    (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg))) = _
  rw [nerve.δ₂_mk₂_eq]
  rfl

/-- Both entire vertex triangles are the actual degenerate chosen-zero simplex. -/
theorem weakObjectCompositionFamily_vertex (e : Fin 2) :
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) ⊗ₘ 𝟙 Δ[2]) ≫
        bisimplexFamily W (W.weakObjectCompositionPrism f g hf hg)
          (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) =
      SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  have hobj : ∀ p,
      ((((SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) ⊗ₘ 𝟙 Δ[2]) ≫
        bisimplexFamily W (W.weakObjectCompositionPrism f g hf hg)
          (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg)).app n) z).val.obj p =
        W.zero := by
    intro p
    change (W.weakObjectCompositionPrism f g hf hg).obj
      (z.2.down.toOrderHom p.1, interval e e le_rfl) = W.zero
    generalize z.2.down.toOrderHom p.1 = k
    fin_cases k <;> fin_cases e <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q a
  have hz := W.isZero
  rw [← hobj p] at hz
  exact hz.eq_of_src _ _

end CategoryTheory.Waldhausen.Structure
