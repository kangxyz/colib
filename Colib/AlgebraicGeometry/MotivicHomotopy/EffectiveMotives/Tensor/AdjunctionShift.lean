/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.Algebra.Group.Int.Defs

/-! # Shift equivariance of adjoint transposition -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction
universe u v u' v'
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [HasShift A ℤ] [HasShift B ℤ]
  {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) [L.CommShift ℤ] [R.CommShift ℤ]
  [a.CommShift ℤ]

/-- The transpose of a shifted morphism uses the original comparison of each adjoint. -/
theorem homEquiv_shift_transport {X : A} {Y : B} (f : L.obj X ⟶ Y) (n : ℤ) :
    a.homEquiv (X⟦n⟧) (Y⟦n⟧) ((L.commShiftIso n).hom.app X ≫ f⟦n⟧') ≫
      (R.commShiftIso n).hom.app Y = (a.homEquiv X Y f)⟦n⟧' := by
  have h₁ : R.map (f⟦n⟧') ≫ (R.commShiftIso n).hom.app Y =
      (R.commShiftIso n).hom.app (L.obj X) ≫ (R.map f)⟦n⟧' :=
    (R.commShiftIso n).hom.naturality f
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [h₁, ← a.shift_unit_app_assoc n X]

end CategoryTheory.Adjunction
