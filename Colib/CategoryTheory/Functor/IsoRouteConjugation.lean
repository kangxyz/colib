/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Colib.Util.References

/-!
# Conjugating two-square routes by evaluation isomorphisms

For six categories with independent object and morphism universes, replacing the three
vertical functors by specified isomorphic functors conjugates their two-square route only
at its outer endpoints. The intermediate comparison cancels inside the genuine route,
which retains every functor associator. No compatibility premise is required.
The current consumer normalizes the geometric small evaluation functors to model evaluation.
The intended upstream owner is `Aglib.CategoryTheory.Functor.IsoRouteConjugation`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ w₀ z₀ w₁ z₁ w₂ z₂
namespace CategoryTheory.Functor

variable {A₀ : Type u₀} [Category.{v₀} A₀]
  {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {B₀ : Type w₀} [Category.{z₀} B₀]
  {B₁ : Type w₁} [Category.{z₁} B₁] {B₂ : Type w₂} [Category.{z₂} B₂]
  {a : A₀ ⥤ A₁} {b : A₁ ⥤ A₂} {N : B₀ ⥤ B₁} {M : B₁ ⥤ B₂}
  {E₀ E₀' : A₀ ⥤ B₀} {E₁ E₁' : A₁ ⥤ B₁} {E₂ E₂' : A₂ ⥤ B₂}

/-- Conjugate an actual square by the specified source and target evaluation isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IsoRouteConjugation.lean:34"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def isoSquareConjugate (s : a ⋙ E₁ ≅ E₀ ⋙ N) (e₀ : E₀ ≅ E₀') (e₁ : E₁ ≅ E₁') :
    a ⋙ E₁' ≅ E₀' ⋙ N :=
  isoWhiskerLeft a e₁.symm ≪≫ s ≪≫ isoWhiskerRight e₀ N

/-- Paste two actual square isomorphisms, retaining their original functor associators. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IsoRouteConjugation.lean:39"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def isoSquareRoute (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) :
    (a ⋙ b) ⋙ E₂ ≅ E₀ ⋙ (N ⋙ M) :=
  Functor.associator a b E₂ ≪≫ isoWhiskerLeft a t ≪≫
    (Functor.associator a E₁ M).symm ≪≫ isoWhiskerRight s M ≪≫
    Functor.associator E₀ N M

/-- The intermediate normalization cancels, leaving the original route conjugated at its ends. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IsoRouteConjugation.lean:46"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
theorem isoSquareRoute_conjugate (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M)
    (e₀ : E₀ ≅ E₀') (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') :
    isoSquareRoute (isoSquareConjugate s e₀ e₁) (isoSquareConjugate t e₁ e₂) =
      isoWhiskerLeft (a ⋙ b) e₂.symm ≪≫ isoSquareRoute s t ≪≫
        isoWhiskerRight e₀ (N ⋙ M) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, isoSquareConjugate, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← M.map_comp_assoc, e₁.hom_inv_id_app, M.map_id, Category.id_comp]

end CategoryTheory.Functor
