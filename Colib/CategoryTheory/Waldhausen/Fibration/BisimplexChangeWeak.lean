/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.SConstruction.BisimplexFamily
public import Colib.CategoryTheory.Waldhausen.Rows.WeakObjectSimplex

/-! # Whole bisimplex-family transport under nested weak equivalences

Every simplex degree and every mixed grid map is unchanged by the literal identity
functor. The weak-arrow grid comparison keeps the specified chosen-zero equality.
No zero morphisms, saturation or realization are required.
-/
/- Implementation provenance:
   `Quillen/Waldhausen/Fibration/BisimplexChangeWeak.lean`,
   lines 25–36,49–62, at Quillen commit
   `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original names, hypotheses,
   maps and independent universe parameters are retained. Source-only adaptation;
   native compilation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {n m : ℕ}
  (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ V.cof V.weq F)
  (hG : IsSimplex₂ N.coarse.cof N.coarse.weq F)

/-- The original change-of-weak-equivalence map leaves the entire fine grid unchanged. -/
theorem bisimplexFamily_changeWeak :
    bisimplexFamily V F hF ≫ sSetMap (changeWeak_exact N) =
      bisimplexFamily N.coarse F hG := by
  ext k z
  apply Subtype.ext
  exact Functor.comp_id _

/-- The original weak-arrow grid depends on the chosen zero, but not its weakness certificate. -/
theorem weakObjectSimplex_val_of_zero_eq (W : Structure C) (h0 : V.zero = W.zero)
    {A B : C} (f : A ⟶ B) (hf : V.weq f) (hg : W.weq f) :
    (V.weakObjectSimplex f hf).val = (W.weakObjectSimplex f hg).val := by
  cases V
  cases W
  cases h0
  refine CategoryTheory.Functor.ext (fun p ↦ ?_) ?_
  · rcases p with ⟨s, p⟩
    fin_cases s <;> rfl
  · rintro ⟨s, p⟩ ⟨t, q⟩ a
    fin_cases s <;> fin_cases t <;>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;>
      first | rfl | exact False.elim (by have h := (leOfHom a).1; simp at h)

end CategoryTheory.Waldhausen.Fibration
