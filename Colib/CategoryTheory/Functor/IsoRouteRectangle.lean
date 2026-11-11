/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Colib.CategoryTheory.Functor.IsoRouteConjugation

/-!
# Conjugating an actual route rectangle at its evaluation corners

A commuting rectangle of functor isomorphisms remains commuting when its two evaluation
functors are replaced through specified genuine isomorphisms. The source routes agree by
an explicit equality, whose transport remains in the normalized rectangle. All four
categories have independent object and morphism universes. No new compatibility premise
is required beyond the original rectangle. The current consumer normalizes the original
small-model tensor input square to its actual model evaluation functors.
The intended upstream owner is `Colib.CategoryTheory.Functor.IsoRouteRectangle`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₀ v₀ u₂ v₂ w₀ z₀ w₂ z₂
namespace CategoryTheory.Functor

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₀ : Type w₀} [Category.{z₀} D₀] {D₂ : Type w₂} [Category.{z₂} D₂]
  {a b : C₀ ⥤ C₂} {N M : D₀ ⥤ D₂}
  {E₀ E₀' : C₀ ⥤ D₀} {E₂ E₂' : C₂ ⥤ D₂}

/-- Conjugating the actual corner evaluations preserves the original inverse-route rectangle. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IsoRouteRectangle.lean:34"
  "adaptation" "Original full rectangle, actual source transport and both normalized routes."]
theorem isoSquareConjugate_rectangle
    (L : a ⋙ E₂ ≅ E₀ ⋙ N) (R : b ⋙ E₂ ≅ E₀ ⋙ M) (r : N ≅ M) (h : a = b)
    (e₀ : E₀ ≅ E₀') (e₂ : E₂ ≅ E₂')
    (hsq : whiskerLeft E₀ r.hom ≫ R.inv =
      L.inv ≫ eqToHom (congrArg (fun G => G ⋙ E₂) h)) :
    whiskerLeft E₀' r.hom ≫ (isoSquareConjugate R e₀ e₂).inv =
      (isoSquareConjugate L e₀ e₂).inv ≫
        eqToHom (congrArg (fun G => G ⋙ E₂') h) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id] at hsq ⊢
  simp only [isoSquareConjugate, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, Category.assoc]
  rw [whiskerLeft_comp_whiskerRight_assoc, reassoc_of% hsq]

end CategoryTheory.Functor
