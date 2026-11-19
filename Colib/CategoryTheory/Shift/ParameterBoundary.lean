/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # The native signed parameter boundary under a shift-compatible functor -/

@[expose] public section
namespace CategoryTheory
open CategoryTheory.Functor
variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ] (E : C ⥤ D) [E.CommShift ℤ]

/-- Transport of the literal additive-shift boundary. In motivic applications
`t = -(q+1)` and `s = -q`; the final shift by one is retained. -/
theorem parameter_boundary_transport {X N : C} {N' : D}
    (t s : ℤ) (hs : t + 1 = s) (θ : X ≅ N⟦t⟧) (a : E.obj N ≅ N') :
    let θ' := E.mapIso θ ≪≫ (E.commShiftIso t).app N ≪≫
      (shiftFunctor D t).mapIso a
    E.map ((shiftFunctorAdd' C t 1 s hs).hom.app N ≫ θ.inv⟦(1 : ℤ)⟧') ≫
      (E.commShiftIso (1 : ℤ)).hom.app X =
    (E.commShiftIso s).hom.app N ≫ a.hom⟦s⟧' ≫
      (shiftFunctorAdd' D t 1 s hs).hom.app N' ≫ θ'.inv⟦(1 : ℤ)⟧' := by
  intro θ'
  have hc := congrArg (fun z => z.hom.app N) (E.commShiftIso_add' hs)
  simp only [CommShift.isoAdd'_hom_app] at hc
  rw [hc]
  dsimp only [θ', Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_map, Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [E.commShiftIso_hom_naturality]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]

end CategoryTheory
