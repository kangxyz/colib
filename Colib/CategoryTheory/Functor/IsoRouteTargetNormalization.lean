/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Functor.IsoRouteRectangle

/-! # Actual route rectangles through horizontal functor normalizations

Specified isomorphisms of the horizontal functors transport both edges of a two-square
route. Their total normalization conjugates the original input rectangle. The current consumer
is the genuine supported tensor input and evaluation rectangle. The intended
upstream owner is `Aglib.CategoryTheory.Functor.IsoRouteTargetNormalization`.
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
  {a : A₀ ⥤ A₁} {b : A₁ ⥤ A₂}
  {N N' : B₀ ⥤ B₁} {M M' : B₁ ⥤ B₂}
  {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}

/-- Independently normalizing two target functors keeps the original two-edge route. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IsoRouteTargetNormalization.lean:32"
  "adaptation" "Original full rectangle, actual source transport and both normalized routes."]
theorem isoSquareRoute_targetNormalization
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M)
    (n : N ≅ N') (m : M ≅ M') :
    isoSquareRoute (s ≪≫ isoWhiskerLeft E₀ n) (t ≪≫ isoWhiskerLeft E₁ m) =
      isoSquareRoute s t ≪≫
        isoWhiskerLeft E₀ (isoWhiskerRight n M ≪≫ isoWhiskerLeft N' m) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc]
  rw [← m.hom.naturality_assoc, ← m.hom.naturality]

section Rectangle
variable {c d : A₀ ⥤ A₂} {P P' Q Q' : B₀ ⥤ B₂}

/-- A total horizontal normalization preserves the complete original inverse-route rectangle. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IsoRouteTargetNormalization.lean:51"
  "adaptation" "Original full rectangle, actual source transport and both normalized routes."]
theorem isoSquareTargetNormalization_rectangle
    (L : c ⋙ E₂ ≅ E₀ ⋙ P) (R : d ⋙ E₂ ≅ E₀ ⋙ Q)
    (r : P ≅ Q) (h : c = d) (n : P ≅ P') (m : Q ≅ Q')
    (hsq : whiskerLeft E₀ r.hom ≫ R.inv =
      L.inv ≫ eqToHom (congrArg (fun G => G ⋙ E₂) h)) :
    whiskerLeft E₀ (n.symm ≪≫ r ≪≫ m).hom ≫
        (R ≪≫ isoWhiskerLeft E₀ m).inv =
      (L ≪≫ isoWhiskerLeft E₀ n).inv ≫
        eqToHom (congrArg (fun G => G ⋙ E₂) h) := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, isoWhiskerLeft_inv,
    whiskerLeft_comp, Category.assoc]
  rw [show whiskerLeft E₀ m.hom ≫ (whiskerLeft E₀ m.inv ≫ R.inv) = R.inv from
    (isoWhiskerLeft E₀ m).hom_inv_id_assoc R.inv, hsq]


end Rectangle
end CategoryTheory.Functor

namespace CategoryTheory.Functor

attribute [colib_tag "COL-0559"] isoSquareTargetNormalization_rectangle

end CategoryTheory.Functor
