/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-! # Compatible dual Waldhausen structures

The compatibility is on literal weak maps and actual zero-corner kernel–cokernel
squares. No statement about S-constructions or K-theory is part of this input.

Implementation provenance: `Quillen/Waldhausen/Duality/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual maps, structural hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.Waldhausen

/-- The exact structural compatibility required to reverse quotient grids. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Duality/Basic.lean:22-28" "adaptation"
    "Literal weak maps and zero-corner cofiber/fiber squares"]
structure IsCompatibleDual {C : Type u} [Category.{v} C]
    (W : Structure C) (Wd : Structure Cᵒᵖ) : Prop where
  /-- Weakness is preserved and reflected by reversing the actual morphism. -/
  weak {A B : C} (f : A ⟶ B) : W.weq f ↔ Wd.weq f.op
  /-- Cofiber squares with any actual zero corner are exactly dual fiber squares. -/
  cofiber {A B Z Q : C} (i : A ⟶ B) (z : A ⟶ Z) (q : B ⟶ Q) (s : Z ⟶ Q)
    (hZ : IsZero Z) :
    (W.cof i ∧ IsPushout i z q s) ↔ (Wd.cof q.op ∧ IsPullback i z q s)

end CategoryTheory.Waldhausen
