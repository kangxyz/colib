/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.SConstruction.CofiberObjectSimplex
public import Colib.CategoryTheory.Waldhausen.Rows.CofiberTwoComparison

/-! # Whole cofiber-simplex transport under nested weak equivalences

The literal grid, its chosen zero, both cofibration certificates and both displayed
pushout certificates are retained. The identity-cofiber comparison uses its actual
chosen-zero quotient. These categorical equalities require no realization.
-/
/- Implementation provenance:
   `Quillen/Waldhausen/Fibration/CofiberObjectChangeWeak.lean`,
   lines 20–44, at Quillen commit
   `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original names, hypotheses,
   maps and independent universe parameters are retained. Source-only adaptation;
   native compilation remains pending. -/
/- Implementation provenance:
   `Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean`,
   lines 74–83, at Quillen commit
   `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original names, hypotheses,
   maps and independent universe parameters are retained. Source-only adaptation;
   native compilation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V)
  {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : V.cof i) (hi' : N.coarse.cof i)
  (hQ : IsPushout i (0 : A ⟶ V.zero) q (0 : V.zero ⟶ Q))
  (hQ' : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- With the same specified zero, the genuine cofiber triangle keeps every original grid map. -/
theorem cofiberObjectSimplex_val_of_zero_eq
    (W : Structure C) (h0 : V.zero = W.zero) (hw : W.cof i)
    (hW : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    (V.cofiberObjectSimplex i q hi hQ).val = (W.cofiberObjectSimplex i q hw hW).val := by
  cases V
  cases W
  cases h0
  rfl

/-- The unchanged localization simplicial map sends the actual fine triangle to its coarse one. -/
theorem cofiberObjectSimplex_changeWeak :
    (sSetMap (changeWeak_exact N)).app (op ⦋2⦌) (V.cofiberObjectSimplex i q hi hQ) =
      N.coarse.cofiberObjectSimplex i q hi' hQ' := by
  apply Subtype.ext
  change (V.cofiberObjectSimplex i q hi hQ).val ⋙ 𝟭 C = _
  rw [Functor.comp_id]
  exact cofiberObjectSimplex_val_of_zero_eq i q hi hQ N.coarse N.zero_eq.symm hi' hQ'

section Identity
variable (A : C)

/-- The entire identity triangle retains its actual grid whenever the chosen zeros agree. -/
theorem identityCofiberSimplex_val_of_zero_eq (W : Structure C) (h0 : V.zero = W.zero) :
    (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
        (cofiberTwo_identity_square V)).val =
      (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W)).val := by
  cases V
  cases W
  cases h0
  rfl

end Identity
end CategoryTheory.Waldhausen.Fibration
