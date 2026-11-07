/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.CofiberTwoComparison
public import Colib.CategoryTheory.Waldhausen.Rows.NerveBridge


/-! # The genuine nerve prism of the original weak cofiber row

The actual weak row arrow gives a genuine bisimplex in S-degree two and nerve degree one.
Every horizontal row and every mixed map are the original chain-to-grid construction.
-/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/SConstruction/Rows/CofiberTwoPrism.lean`
   at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
   Original objects, maps, hypotheses and universe parameters are retained.
   Source-only preparation; native validation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The actual one-arrow weak chain retains the specified row comparison. -/
def cofiberTwoWeakArrow :
    (⟨cofiberTwoRow W (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W)⟩ : WeakRows W ⦋2⦌) ⟶
    ⟨cofiberTwoRow W i q hi hQ⟩ :=
  ⟨cofiberTwoRowComparison W i q hi hQ, cofiberTwoRowComparison_weak W i q hi hwi hQ⟩

/-- The original nerve prism, with its separate interval and nerve coordinates. -/
def cofiberTwoPrism : Grid₂ ⦋2⦌ ⦋1⦌ ⥤ C :=
  weakChainToGrid W (ComposableArrows.mk₁ (cofiberTwoWeakArrow W i q hi hwi hQ))

/-- The actual row, quotient and weak-arrow predicates certify the whole prism. -/
theorem cofiberTwoPrism_isSimplex₂ :
    IsSimplex₂ W.cof W.weq (cofiberTwoPrism W i q hi hwi hQ) :=
  weakChainToGrid_isSimplex₂ W _

/-- Nerve time zero is the entire original identity-cofiber row. -/
theorem cofiberTwoPrism_zero :
    gridRestriction 0 ⋙ cofiberTwoPrism W i q hi hwi hQ =
      cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp) :=
  weakChainToGrid_row W _ 0

/-- Nerve time one is the entire original displayed quotient row. -/
theorem cofiberTwoPrism_one :
    gridRestriction 1 ⋙ cofiberTwoPrism W i q hi hwi hQ =
      cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ) :=
  weakChainToGrid_row W _ 1

end CategoryTheory.Waldhausen.QuotientRows
