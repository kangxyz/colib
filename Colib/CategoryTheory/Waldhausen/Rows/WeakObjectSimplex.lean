/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRow
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
