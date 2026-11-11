/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.CategoryTheory.Functor.IsoRouteTargetNormalization
public import Colib.CategoryTheory.Waldhausen.AsSmall.RouteRectangle
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.AsSmall

section
universe u₀ v₀ u₂ v₂ w₀ z₀ w₂ z₂
namespace CategoryTheory.Functor

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₀ : Type w₀} [Category.{z₀} D₀] {D₂ : Type w₂} [Category.{z₂} D₂]
  {a b : C₀ ⥤ C₂} {N M : D₀ ⥤ D₂}
  {E₀ E₀' : C₀ ⥤ D₀} {E₂ E₂' : C₂ ⥤ D₂}

example
    (L : a ⋙ E₂ ≅ E₀ ⋙ N) (R : b ⋙ E₂ ≅ E₀ ⋙ M) (r : N ≅ M) (h : a = b)
    (e₀ : E₀ ≅ E₀') (e₂ : E₂ ≅ E₂')
    (hsq : whiskerLeft E₀ r.hom ≫ R.inv =
      L.inv ≫ eqToHom (congrArg (fun G => G ⋙ E₂) h)) :
    whiskerLeft E₀' r.hom ≫ (isoSquareConjugate R e₀ e₂).inv =
      (isoSquareConjugate L e₀ e₂).inv ≫
        eqToHom (congrArg (fun G => G ⋙ E₂') h) :=
  isoSquareConjugate_rectangle L R r h e₀ e₂ hsq

end CategoryTheory.Functor
end

section
universe u₀ v₀ u₁ v₁ u₂ v₂ w₀ z₀ w₁ z₁ w₂ z₂
namespace CategoryTheory.Functor

variable {A₀ : Type u₀} [Category.{v₀} A₀]
  {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {B₀ : Type w₀} [Category.{z₀} B₀]
  {B₁ : Type w₁} [Category.{z₁} B₁] {B₂ : Type w₂} [Category.{z₂} B₂]
  {a : A₀ ⥤ A₁} {b : A₁ ⥤ A₂}
  {N N' : B₀ ⥤ B₁} {M M' : B₁ ⥤ B₂}
  {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}

example
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M)
    (n : N ≅ N') (m : M ≅ M') :
    isoSquareRoute (s ≪≫ isoWhiskerLeft E₀ n) (t ≪≫ isoWhiskerLeft E₁ m) =
      isoSquareRoute s t ≪≫
        isoWhiskerLeft E₀ (isoWhiskerRight n M ≪≫ isoWhiskerLeft N' m) :=
  isoSquareRoute_targetNormalization s t n m

section Rectangle
variable {c d : A₀ ⥤ A₂} {P P' Q Q' : B₀ ⥤ B₂}
example
    (L : c ⋙ E₂ ≅ E₀ ⋙ P) (R : d ⋙ E₂ ≅ E₀ ⋙ Q)
    (r : P ≅ Q) (h : c = d) (n : P ≅ P') (m : Q ≅ Q')
    (hsq : whiskerLeft E₀ r.hom ≫ R.inv =
      L.inv ≫ eqToHom (congrArg (fun G => G ⋙ E₂) h)) :
    whiskerLeft E₀ (n.symm ≪≫ r ≪≫ m).hom ≫
        (R ≪≫ isoWhiskerLeft E₀ m).inv =
      (L ≪≫ isoWhiskerLeft E₀ n).inv ≫
        eqToHom (congrArg (fun G => G ⋙ E₂) h) :=
  isoSquareTargetNormalization_rectangle L R r h n m hsq

end Rectangle
end CategoryTheory.Functor
end

section
universe u v w z
namespace CategoryTheory.Waldhausen

variable {C₀ C₁ C₂ C₃ : Type u} [Category.{v} C₀] [Category.{v} C₁]
  [Category.{v} C₂] [Category.{v} C₃]
  {D₀ D₁ D₂ D₃ : Type w} [Category.{z} D₀] [Category.{z} D₁]
  [Category.{z} D₂] [Category.{z} D₃]
  {a : C₀ ⥤ C₁} {b : C₁ ⥤ C₃} {c : C₀ ⥤ C₂} {d : C₂ ⥤ C₃}
  {P : D₀ ⥤ D₁} {M : D₁ ⥤ D₃} {Q : D₀ ⥤ D₂} {N : D₂ ⥤ D₃}
  {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}

example (s : a ⋙ E₁ ≅ E₀ ⋙ P) :
    a ⋙ (E₁ ⋙ AsSmall.up.{z, w, 0}) ≅
      (E₀ ⋙ AsSmall.up.{z, w, 0}) ⋙ asSmallFunctor P :=
  asSmallSquareIso s

example (r : P ⋙ M ≅ Q ⋙ N) :
    asSmallFunctor P ⋙ asSmallFunctor M ≅
      asSmallFunctor Q ⋙ asSmallFunctor N :=
  asSmallRectangleIso r

example
    (s : a ⋙ E₁ ≅ E₀ ⋙ P) (t : b ⋙ E₃ ≅ E₁ ⋙ M)
    (v : c ⋙ E₂ ≅ E₀ ⋙ Q) (w : d ⋙ E₃ ≅ E₂ ⋙ N)
    (r : P ⋙ M ≅ Q ⋙ N) (h : a ⋙ b = c ⋙ d)
    (hsq : whiskerLeft E₀ r.hom ≫ (isoSquareRoute v w).inv =
      (isoSquareRoute s t).inv ≫ eqToHom (congrArg (fun F => F ⋙ E₃) h)) :
    whiskerLeft (E₀ ⋙ AsSmall.up.{z, w, 0}) (asSmallRectangleIso r).hom ≫
        (isoSquareRoute (asSmallSquareIso v) (asSmallSquareIso w)).inv =
      (isoSquareRoute (asSmallSquareIso s) (asSmallSquareIso t)).inv ≫
        eqToHom (congrArg (fun F => F ⋙ (E₃ ⋙ AsSmall.up.{z, w, 0})) h) :=
  asSmallRouteRectangle s t v w r h hsq

end CategoryTheory.Waldhausen
end

end
