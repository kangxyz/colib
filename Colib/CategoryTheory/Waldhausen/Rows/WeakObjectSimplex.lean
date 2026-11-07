/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRow
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Colib.CategoryTheory.Waldhausen.Rows.NerveBridge

/-! # The actual weak-arrow simplex of original quotient rows

Implementation provenance: unchanged native definitions extracted from `WeakRelations` in
`Colib/KTheory/Waldhausen/GrothendieckComparison/`, frozen parent `20c70502`.
The original implementation is `Quillen/Waldhausen/GrothendieckComparison/WeakRelations.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
names, namespaces, declaration bodies, hypotheses and universe parameters are unchanged.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
open QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B : C} (f : A ⟶ B) (hf : W.weq f)

/-- The original weak arrow between the actual one-step quotient rows. -/
def oneWeakArrow : (⟨(oneEmbedding W).obj A⟩ : WeakRows W ⦋1⦌) ⟶
    ⟨(oneEmbedding W).obj B⟩ :=
  ⟨(oneEmbedding W).map f, (oneEmbedding_exact W).weak f hf⟩

/-- The original weak-arrow square, read as a diagonal one-simplex. -/
def weakObjectSimplex : (sSet W.cof W.weq) _⦋1⦌ :=
  ⟨weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)),
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp (weakChainToGrid_isSimplex₂ W _)⟩

end CategoryTheory.Waldhausen.Structure

/- Implementation provenance:
   `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionPrism.lean`,
   lines 31–36, at Quillen commit
   `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original names, hypotheses,
   maps and independent universe parameters are retained. Source-only adaptation;
   native compilation remains pending. -/
namespace CategoryTheory.Waldhausen.Structure
open QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- The one-row embedding preserves the original composite as an actual weak-row arrow. -/
theorem oneWeakArrow_comp :
    W.oneWeakArrow f hf ≫ W.oneWeakArrow g hg =
      W.oneWeakArrow (f ≫ g) (W.weq.comp_mem _ _ hf hg) := by
  apply WideSubcategory.hom_ext
  exact ((oneEmbedding W).map_comp f g).symm

end CategoryTheory.Waldhausen.Structure

/- Implementation provenance:
   `Quillen/Waldhausen/AutomorphismKOne.lean`,
   lines 129–131,153–180, at Quillen commit
   `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original names, hypotheses,
   maps and independent universe parameters are retained. Source-only adaptation;
   native compilation remains pending. -/
namespace CategoryTheory.Waldhausen
open QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- A strictly zero-preserving exact functor keeps every cell of the original weak-arrow square. -/
theorem weakObjectSimplex_postcompose (h0 : F.obj V.zero = W.zero)
    {A B : C} (f : A ⟶ B) (hf : V.weq f) :
    (V.weakObjectSimplex f hf).val ⋙ F =
      (W.weakObjectSimplex (F.map f) (hF.weak f hf)).val := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · rintro ⟨s, ⟨⟨i, j⟩, hij⟩⟩
    fin_cases s <;> fin_cases i <;> fin_cases j
    all_goals first
      | exact h0
      | rfl
  · rintro ⟨s, ⟨⟨i, j⟩, hij⟩⟩ ⟨t, ⟨⟨k, l⟩, hkl⟩⟩ a
    have hst := (leOfHom a).1
    change s.val ≤ t.val at hst
    change i.val ≤ j.val at hij
    change k.val ≤ l.val at hkl
    fin_cases s <;> fin_cases t <;> fin_cases i <;> fin_cases j <;>
      fin_cases k <;> fin_cases l
    all_goals try { simp at hst }
    all_goals try { simp at hij }
    all_goals try { simp at hkl }
    all_goals first
      | omega
      | exact (hF.zero V.isZero).eq_of_src _ _
      | exact (hF.zero V.isZero).eq_of_tgt _ _
      | simp [Structure.weakObjectSimplex, weakChainToGrid, Structure.oneWeakArrow,
          oneEmbedding, oneDiagram, oneIndex, oneChain, ComposableArrows.mk₁,
          ComposableArrows.mk₂]

end CategoryTheory.Waldhausen
