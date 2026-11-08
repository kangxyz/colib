/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.Rows.Basic

/-!
# The literal two-step row of a displayed cofiber sequence

The six interval objects are `(0, A, B, 0, Q, 0)`, using the chosen zero.
The two nontrivial short arrows are the displayed `i` and `q`; the other strict
arrows are literal zero maps. The supplied cofiber square proves the row axioms.

Implementation provenance: the complete mathematical content of
`Quillen/Waldhausen/SConstruction/Rows/CofiberTwoRow.lean` (214 lines), together with
only `cofiberTwo_identity_square` from
`Quillen/Waldhausen/SConstruction/Rows/CofiberTwoComparison.lean`, lines 93–98,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. No row-comparison or prism construction
is included. Native row-completion constructions are not duplicated.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)

/-- The six literal objects of the displayed two-step quotient row. -/
abbrev cofiberTwoObject (p : Interval ⦋2⦌) : C :=
  match p.val.1.val, p.val.2.val with
  | 0, 1 => A
  | 0, 2 => B
  | 1, 2 => Q
  | _, _ => W.zero

/-- The actual original cofibration and quotient, with zero maps on the other strict intervals. -/
def cofiberTwoMap {p r : Interval ⦋2⦌} (_f : p ⟶ r) :
    cofiberTwoObject W (A := A) (B := B) (Q := Q) p ⟶
      cofiberTwoObject W (A := A) (B := B) (Q := Q) r := by
  classical
  by_cases h : p = r
  · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h)
  · by_cases h₁ : p = interval 0 1 (by decide) ∧ r = interval 0 2 (by decide)
    · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₁.1) ≫
        i ≫ eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₁.2.symm)
    · by_cases h₂ : p = interval 0 2 (by decide) ∧ r = interval 1 2 (by decide)
      · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₂.1) ≫
          q ≫ eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₂.2.symm)
      · exact 0

private theorem cofiberTwoMap_comp_00
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 0 0 (by decide))
    (g : interval 0 0 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 0 ∧ b.val ≤ 0 := leOfHom f
  have hg : 0 ≤ c.val ∧ 0 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _

private theorem cofiberTwoMap_comp_01
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 0 1 (by decide))
    (g : interval 0 1 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 0 ∧ b.val ≤ 1 := leOfHom f
  have hg : 0 ≤ c.val ∧ 1 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval]

private theorem cofiberTwoMap_comp_02 (hiq : i ≫ q = 0)
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 0 2 (by decide))
    (g : interval 0 2 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 0 ∧ b.val ≤ 2 := leOfHom f
  have hg : 0 ≤ c.val ∧ 2 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval, hiq]

private theorem cofiberTwoMap_comp_11
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 1 1 (by decide))
    (g : interval 1 1 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 1 ∧ b.val ≤ 1 := leOfHom f
  have hg : 1 ≤ c.val ∧ 1 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval]

private theorem cofiberTwoMap_comp_12
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 1 2 (by decide))
    (g : interval 1 2 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 1 ∧ b.val ≤ 2 := leOfHom f
  have hg : 1 ≤ c.val ∧ 2 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval]

private theorem cofiberTwoMap_comp_22
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 2 2 (by decide))
    (g : interval 2 2 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 2 ∧ b.val ≤ 2 := leOfHom f
  have hg : 2 ≤ c.val ∧ 2 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _

/-- The literal maps form a functor exactly when the displayed composite is zero. -/
def cofiberTwoDiagram (hiq : i ≫ q = 0) : Interval ⦋2⦌ ⥤ C where
  obj := cofiberTwoObject W (A := A) (B := B) (Q := Q)
  map := cofiberTwoMap W i q
  map_id p := by simp [cofiberTwoMap]
  map_comp {p r s} f g := by
    rcases r with ⟨⟨a, b⟩, hab⟩
    change a.val ≤ b.val at hab
    fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;> first
    | omega
    | exact cofiberTwoMap_comp_00 W i q f g
    | exact cofiberTwoMap_comp_01 W i q f g
    | exact cofiberTwoMap_comp_02 W i q hiq f g
    | exact cofiberTwoMap_comp_11 W i q f g
    | exact cofiberTwoMap_comp_12 W i q f g
    | exact cofiberTwoMap_comp_22 W i q f g

/-- The displayed original cofiber square supplies every actual two-row axiom. -/
theorem cofiberTwoDiagram_isRow (hiq : i ≫ q = 0) (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    IsRow W (cofiberTwoDiagram W i q hiq) where
  zero k := by
    fin_cases k <;> exact W.isZero
  cofibration a b c hab hbc := by
    have hz (X : C) : W.cof (0 : W.zero ⟶ X) := by
      convert W.cof_zero X using 1
      exact W.isZero.eq_of_src _ _
    change a.val ≤ b.val at hab
    change b.val ≤ c.val at hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      dsimp at hab hbc ⊢ <;>
      solve
      | omega
      | exact W.cof.id_mem _
      | exact hz _
      | simpa [cofiberTwoDiagram, cofiberTwoMap, interval] using hi
  quotient a b c hab hbc := by
    change a.val ≤ b.val at hab
    change b.val ≤ c.val at hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      dsimp at hab hbc ⊢ <;>
      solve
      | omega
      | exact IsPushout.id_horiz _
      | exact IsPushout.of_id_snd
      | simpa [cofiberTwoDiagram, cofiberTwoMap, interval] using hQ

/-- The original quotient square itself gives the required zero composite. -/
theorem cofiberTwo_comp_eq_zero
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) : i ≫ q = 0 := by
  simpa only [zero_comp] using hQ.w

/-- The actual displayed quotient sequence as an object of the original S-row category. -/
def cofiberTwoRow (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) : Obj W ⦋2⦌ :=
  ⟨cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ),
    cofiberTwoDiagram_isRow W i q (cofiberTwo_comp_eq_zero W i q hQ) hi hQ⟩

/-- The identity row has its literal chosen-zero quotient, supplied by the actual identity square.
-/
theorem cofiberTwo_identity_square :
    IsPushout (𝟙 A) (0 : A ⟶ W.zero) (0 : A ⟶ W.zero) (0 : W.zero ⟶ W.zero) := by
  convert IsPushout.id_horiz (0 : A ⟶ W.zero) using 1
  exact W.isZero.eq_of_src _ _

attribute [colib_ref "Waldhausen1985"
  "Section 1.3, definition of $S_n C$ and face maps, pp. 328-329" "ingredient"
  "The S_2 interval-functor construction for a displayed cofiber square; the native literal
    row retains its specified quotient, arrows and chosen-zero diagonal objects"]
  cofiberTwoRow

end CategoryTheory.Waldhausen.QuotientRows
