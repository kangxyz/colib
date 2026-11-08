/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.CofiberTwoFaces


/-! # The actual weak row comparison for a cofiber prism

The original gluing axiom makes the quotient of a weak cofibration acyclic. This is the
specified zero-to-quotient component required by the actual row comparison.
-/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/SConstruction/Rows/CofiberTwoComparison.lean`
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

/-- Gluing the actual weak cofibration against its identity square proves the original
zero-to-quotient map weak, without an additional acyclicity hypothesis. -/
theorem cofiberTwo_quotient_weak (hi : W.cof i) (hwi : W.weq i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    W.weq (0 : W.zero ⟶ Q) := by
  apply W.gluing (𝟙 A) i (𝟙 W.zero) (0 : W.zero ⟶ Q)
    (W.cof.id_mem A) hi (IsPushout.id_horiz (0 : A ⟶ W.zero)) hQ
  · simp
  · simp
  · simpa only [zero_comp] using (cofiberTwo_comp_eq_zero W i q hQ).symm
  · simp
  · exact W.weq.id_mem A
  · exact hwi
  · exact W.weq.id_mem W.zero

omit [HasZeroMorphisms C] in
/-- Away from the middle and quotient positions, the two original rows have the same object. -/
theorem cofiberTwoComparison_object_eq (p : Interval ⦋2⦌)
    (h02 : p ≠ interval 0 2 (by decide)) (h12 : p ≠ interval 1 2 (by decide)) :
    cofiberTwoObject W (A := A) (B := A) (Q := W.zero) p =
      cofiberTwoObject W (A := A) (B := B) (Q := Q) p := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  change a.val ≤ b.val at hab
  fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
    solve
    | omega
    | rfl
    | exact False.elim (h02 rfl)
    | exact False.elim (h12 rfl)

/-- The original row components are identity on the source, the given arrow on the middle,
and zero-to-quotient on the quotient interval. -/
def cofiberTwoComparisonComponent (p : Interval ⦋2⦌) :
    cofiberTwoObject W (A := A) (B := A) (Q := W.zero) p ⟶
      cofiberTwoObject W (A := A) (B := B) (Q := Q) p := by
  classical
  by_cases h02 : p = interval 0 2 (by decide)
  · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := A) (Q := W.zero)) h02) ≫
      i ≫ eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h02.symm)
  · by_cases h12 : p = interval 1 2 (by decide)
    · exact 0
    · exact eqToHom (cofiberTwoComparison_object_eq W p h02 h12)

/-- The original three components give a natural transformation of the entire two-row diagrams.
-/
def cofiberTwoComparison (hiq : i ≫ q = 0) :
    cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp) ⟶
      cofiberTwoDiagram W i q hiq where
  app := cofiberTwoComparisonComponent W i
  naturality p r f := by
    rcases p with ⟨⟨a, b⟩, hab⟩
    rcases r with ⟨⟨c, d⟩, hcd⟩
    change a.val ≤ b.val at hab
    change c.val ≤ d.val at hcd
    have hf : a.val ≤ c.val ∧ b.val ≤ d.val := leOfHom f
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      dsimp at hab hcd hf ⊢ <;>
      first
      | omega
      | exact W.isZero.eq_of_src _ _
      | exact W.isZero.eq_of_tgt _ _
      | simp only [cofiberTwoDiagram, Fin.isValue, cofiberTwoMap, ↓reduceDIte,
          eqToHom_refl, cofiberTwoComparisonComponent, interval, Nat.reduceAdd,
          Subtype.mk.injEq, Prod.mk.injEq, Fin.reduceEq, and_false,
          and_self, Category.comp_id, Category.id_comp, and_true,
          comp_zero, hiq]
    exact Category.id_comp i

/-- The original row transformation is a morphism between the two genuine quotient rows. -/
def cofiberTwoRowComparison (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    cofiberTwoRow W (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) ⟶ cofiberTwoRow W i q hi hQ :=
  (objects W ⦋2⦌).homMk (cofiberTwoComparison W i q (cofiberTwo_comp_eq_zero W i q hQ))

/-- Every component of the actual row comparison is weak; the zero-to-quotient component
uses the proved original gluing square. -/
theorem cofiberTwoRowComparison_weak (hi : W.cof i) (hwi : W.weq i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    weq W ⦋2⦌ (cofiberTwoRowComparison W i q hi hQ) := by
  rintro ⟨⟨a, b⟩, hab⟩
  change a.val ≤ b.val at hab
  change W.weq (cofiberTwoComparisonComponent W i ⟨(a, b), _⟩)
  fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
    solve
    | omega
    | simp only [cofiberTwoComparisonComponent, interval, Nat.reduceAdd,
        Subtype.mk.injEq, Prod.mk.injEq, Fin.reduceEq, and_false, and_true, and_self,
        ↓reduceDIte, eqToHom_refl, Category.comp_id,
        Category.id_comp]
      first
      | exact W.weq.id_mem _
      | exact hwi
      | exact cofiberTwo_quotient_weak W i q hi hwi hQ

end CategoryTheory.Waldhausen.QuotientRows
