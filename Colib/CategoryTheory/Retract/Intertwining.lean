/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Retract

/-! # Comparison of retracts with conjugate idempotents -/

@[expose] public noncomputable section

namespace CategoryTheory.Retract

/-- An isomorphism intertwining the idempotents of two retracts induces an isomorphism
between their retract objects. -/
def isoOfIntertwining {C : Type*} [Category* C] {A B X Y : C}
    (s : Retract A X) (t : Retract B Y) (e : X ≅ Y)
    (h : (s.r ≫ s.i) ≫ e.hom = e.hom ≫ t.r ≫ t.i) : A ≅ B where
  hom := s.i ≫ e.hom ≫ t.r
  inv := t.i ≫ e.inv ≫ s.r
  hom_inv_id := by
    simp only [Category.assoc]
    have h' : e.hom ≫ t.r ≫ t.i ≫ e.inv ≫ s.r = s.r ≫ s.i ≫ s.r := by
      rw [← Category.assoc t.r t.i, ← Category.assoc e.hom, ← h, Category.assoc,
        Iso.hom_inv_id_assoc, Category.assoc]
    rw [h', ← Category.assoc s.i s.r, s.retract, Category.id_comp]
  inv_hom_id := by
    simp only [Category.assoc]
    have h' : s.r ≫ s.i ≫ e.hom ≫ t.r = e.hom ≫ t.r ≫ t.i ≫ t.r := by
      simpa only [Category.assoc] using congrArg (· ≫ t.r) h
    rw [h', e.inv_hom_id_assoc, ← Category.assoc t.i t.r, t.retract, Category.id_comp]

/-- The comparison is the section, the original isomorphism, and the retraction. -/
theorem isoOfIntertwining_hom {C : Type*} [Category* C] {A B X Y : C}
    (s : Retract A X) (t : Retract B Y) (e : X ≅ Y)
    (h : (s.r ≫ s.i) ≫ e.hom = e.hom ≫ t.r ≫ t.i) :
    (s.isoOfIntertwining t e h).hom = s.i ≫ e.hom ≫ t.r := rfl

end CategoryTheory.Retract
