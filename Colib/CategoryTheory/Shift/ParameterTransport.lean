/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-! # Transport of a parameter square through native shifts

A one-way parameter comparison suffices; it is never inverted.
-/
@[expose] public section
namespace CategoryTheory
open Functor
variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]
  (E : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D)
  [E.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  (τ : F ⋙ E ⟶ E ⋙ G) [NatTrans.CommShift τ ℤ]

/-- An actual parameter square retains its maps under any native integer shift. -/
theorem parameter_square_shift {M N : C} {M' N' : D}
    (f : M ⟶ F.obj N) (g : M' ⟶ G.obj N')
    (a : E.obj M ⟶ M') (b : E.obj N ⟶ N')
    (h : E.map f ≫ τ.app N ≫ G.map b = a ≫ g) (s : ℤ) :
    E.map (f⟦s⟧' ≫ (F.commShiftIso s).inv.app N) ≫
      τ.app (N⟦s⟧) ≫ G.map ((E.commShiftIso s).hom.app N ≫ b⟦s⟧') =
    ((E.commShiftIso s).hom.app M ≫ a⟦s⟧') ≫
      g⟦s⟧' ≫ (G.commShiftIso s).inv.app N' := by
  rw [NatTrans.app_shift]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  rw [E.commShiftIso_hom_naturality]
  rw [← G.commShiftIso_inv_naturality]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t => (E.commShiftIso s).hom.app M ≫
      (shiftFunctor D s).map t ≫ (G.commShiftIso s).inv.app N') h

end CategoryTheory
