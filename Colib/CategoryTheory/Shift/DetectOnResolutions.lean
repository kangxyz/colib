/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-! # Detecting shift squares on resolutions

Only the source functor needs to invert the resolving maps. In particular the
ordinary total-complex target need not invert all quasi-isomorphisms.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D]

/-- Equality can be checked on resolving objects if their maps become epimorphisms
under the source functor; no condition on the target functor is imposed. -/
theorem ext_of_source_epi_resolutions {F G : C ⥤ D} {α β : F ⟶ G}
    (P : C → Prop)
    (hres : ∀ X, ∃ (Y : C) (f : Y ⟶ X), P Y ∧ Epi (F.map f))
    (h : ∀ Y, P Y → α.app Y = β.app Y) : α = β := by
  ext X
  obtain ⟨Y, f, hY, hf⟩ := hres X
  let := hf
  rw [← cancel_epi (F.map f), α.naturality, β.naturality, h Y hY]

/-- Shift compatibility can be checked on resolving objects, provided the source
functor sends every shifted resolving map to an epimorphism. -/
theorem commShift_of_source_epi_resolutions {M : Type*} [AddMonoid M]
    [HasShift C M] [HasShift D M] {F G : C ⥤ D}
    [F.CommShift M] [G.CommShift M] (α : F ⟶ G) (P : C → Prop)
    (hres : ∀ X (a : M), ∃ (Y : C) (f : Y ⟶ X),
      P Y ∧ Epi (F.map ((shiftFunctor C a).map f)))
    (h : ∀ Y, P Y → ∀ a : M,
      (F.commShiftIso a).hom.app Y ≫ (shiftFunctor D a).map (α.app Y) =
        α.app ((shiftFunctor C a).obj Y) ≫ (G.commShiftIso a).hom.app Y) :
    CommShift α M where
  shift_comm a := ext_of_source_epi_resolutions P (fun X => hres X a) (fun Y hY => h Y hY a)

/-- Shift compatibility descends from a resolving functor, without demanding that
functor be essentially surjective in the original category. -/
theorem commShift_of_resolving_whiskerLeft
    {V : Type*} [Category* V] {M : Type*} [AddMonoid M]
    [HasShift V M] [HasShift C M] [HasShift D M]
    (q : V ⥤ C) [q.CommShift M] {F G : C ⥤ D}
    [F.CommShift M] [G.CommShift M] (α : F ⟶ G)
    (hres : ∀ X (a : M), ∃ (Y : V) (f : q.obj Y ⟶ X),
      Epi (F.map ((shiftFunctor C a).map f)))
    [CommShift (Functor.whiskerLeft q α) M] : CommShift α M := by
  refine commShift_of_source_epi_resolutions α (fun X => ∃ Y, q.obj Y = X) ?_ ?_
  · intro X a
    obtain ⟨Y, f, hf⟩ := hres X a
    exact ⟨q.obj Y, f, ⟨Y, rfl⟩, hf⟩
  · rintro _ ⟨Y, rfl⟩ a
    have hc := shift_app_comm (Functor.whiskerLeft q α) a Y
    have hn := α.naturality ((q.commShiftIso a).hom.app Y)
    dsimp at hc hn ⊢
    rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hc
    rw [← cancel_epi (F.map ((q.commShiftIso a).hom.app Y)), ← Category.assoc, hc,
      ← Category.assoc, ← hn, Category.assoc]

end CategoryTheory.NatTrans
