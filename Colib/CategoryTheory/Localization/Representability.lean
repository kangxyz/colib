/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Yoneda

/-!
# Representability from maps before localization

A natural surjection from maps into a chosen object represents a functor
on the localization if maps with equal images agree after localization.
The inverse descends from the original category by full faithfulness of
precomposition with the localization functor.
-/

@[expose] public noncomputable section

open Opposite

universe t v₁ v₂ u₁ u₂

namespace CategoryTheory.Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
  (F : Dᵒᵖ ⥤ Type t) (R : C)

include W

/-- The universal element induced by the identity on the representing object gives
an isomorphism when the strict map comparison is surjective and its fibers agree
after localization. -/
theorem isIso_uliftYonedaEquiv_symm_of_strictMaps
    (e : ∀ X : C, (X ⟶ R) → F.obj (op (Q.obj X)))
    (hNat : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ R),
      e X (f ≫ g) = F.map (Q.map f).op (e Y g))
    (hSurj : ∀ X : C, Function.Surjective (e X))
    (hEq : ∀ (X : C) {f g : X ⟶ R}, e X f = e X g → Q.map f = Q.map g) :
    IsIso ((uliftYonedaEquiv.{t} (X := Q.obj R) (F := F ⋙ uliftFunctor.{v₂, t})).symm
      (ULift.up (e R (𝟙 R)))) := by
  let Y := uliftYoneda.{t}.obj (Q.obj R)
  let F' := F ⋙ uliftFunctor.{v₂, t}
  let α : Y ⟶ F' := uliftYonedaEquiv.{t}.symm (ULift.up (e R (𝟙 R)))
  have hα (X : C) (f : X ⟶ R) :
      α.app (op (Q.obj X)) (ULift.up (Q.map f)) = ULift.up (e X f) := by
    change ULift.up (F.map (Q.map f).op (e R (𝟙 R))) = ULift.up (e X f)
    rw [← hNat, Category.comp_id]
  choose s hs using hSurj
  let β₀ : Q.op ⋙ F' ⟶ Q.op ⋙ Y :=
    { app X := ↾fun a ↦ ULift.up (Q.map (s X.unop a.down))
      naturality X X' f := by
        ext a
        change ULift.up (Q.map (s X'.unop (F.map (Q.map f.unop).op a.down))) =
          ULift.up (Q.map f.unop ≫ Q.map (s X.unop a.down))
        apply congrArg ULift.up
        rw [← Q.map_comp]
        apply hEq
        rw [hs, hNat, hs] }
  let ff := fullyFaithfulWhiskeringLeft Q.op W.op (Type (max v₂ t))
  let β := ff.preimage β₀
  have hβ (X : C) (a : F.obj (op (Q.obj X))) :
      β.app (op (Q.obj X)) (ULift.up a) = ULift.up (Q.map (s X a)) := by
    have h := NatTrans.congr_app (ff.map_preimage β₀) (op X)
    change β.app (op (Q.obj X)) = β₀.app (op X) at h
    exact ConcreteCategory.congr_hom h (ULift.up a : F'.obj (op (Q.obj X)))
  change IsIso α
  refine ⟨β, ?_, ?_⟩
  · apply (uliftYonedaEquiv.{t} (X := Q.obj R)).injective
    change β.app (op (Q.obj R)) (α.app (op (Q.obj R)) (ULift.up (𝟙 _))) = ULift.up (𝟙 _)
    rw [← Q.map_id R, hα, hβ]
    exact congrArg ULift.up (hEq R (hs R _))
  · apply natTrans_ext Q.op W.op
    intro X
    ext a
    obtain ⟨a⟩ := a
    change α.app (op (Q.obj X.unop)) (β.app (op (Q.obj X.unop)) (ULift.up a)) = ULift.up a
    rw [hβ, hα, hs]

/-- The localized morphisms to the representing object are classified by the
original map comparison, with independent hom and value universes. -/
def homEquivOfStrictMaps
    (e : ∀ X : C, (X ⟶ R) → F.obj (op (Q.obj X)))
    (hNat : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ R),
      e X (f ≫ g) = F.map (Q.map f).op (e Y g))
    (hSurj : ∀ X : C, Function.Surjective (e X))
    (hEq : ∀ (X : C) {f g : X ⟶ R}, e X f = e X g → Q.map f = Q.map g)
    (X : C) : (Q.obj X ⟶ Q.obj R) ≃ F.obj (op (Q.obj X)) := by
  let α := (uliftYonedaEquiv.{t} (X := Q.obj R) (F := F ⋙ uliftFunctor.{v₂, t})).symm
    (ULift.up (e R (𝟙 R)))
  haveI : IsIso α := isIso_uliftYonedaEquiv_symm_of_strictMaps Q W F R e hNat hSurj hEq
  exact Equiv.ulift.symm.trans ((asIso (α.app (op (Q.obj X)))).toEquiv.trans Equiv.ulift)

theorem homEquivOfStrictMaps_map
    (e : ∀ X : C, (X ⟶ R) → F.obj (op (Q.obj X)))
    (hNat : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ R),
      e X (f ≫ g) = F.map (Q.map f).op (e Y g))
    (hSurj : ∀ X : C, Function.Surjective (e X))
    (hEq : ∀ (X : C) {f g : X ⟶ R}, e X f = e X g → Q.map f = Q.map g)
    (X : C) (f : X ⟶ R) :
    homEquivOfStrictMaps Q W F R e hNat hSurj hEq X (Q.map f) = e X f := by
  change F.map (Q.map f).op (e R (𝟙 R)) = e X f
  rw [← hNat, Category.comp_id]

theorem homEquivOfStrictMaps_apply
    (e : ∀ X : C, (X ⟶ R) → F.obj (op (Q.obj X)))
    (hNat : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ R),
      e X (f ≫ g) = F.map (Q.map f).op (e Y g))
    (hSurj : ∀ X : C, Function.Surjective (e X))
    (hEq : ∀ (X : C) {f g : X ⟶ R}, e X f = e X g → Q.map f = Q.map g)
    (X : C) (f : Q.obj X ⟶ Q.obj R) :
    homEquivOfStrictMaps Q W F R e hNat hSurj hEq X f = F.map f.op (e R (𝟙 R)) :=
  rfl

end CategoryTheory.Localization
