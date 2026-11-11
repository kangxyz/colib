/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Waldhausen.AsSmall.Whiskering
public import Colib.CategoryTheory.Functor.IsoRouteConjugation

/-! # Common-universe transport of a complete two-route rectangle

The original up/down equivalences lift independently specified square edges and their raw
rectangle. Both complete two-edge routes retain their associators and source equality.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.AsSmall
universe u v w z
namespace CategoryTheory.Waldhausen

variable {C₀ C₁ C₂ C₃ : Type u} [Category.{v} C₀] [Category.{v} C₁]
  [Category.{v} C₂] [Category.{v} C₃]
  {D₀ D₁ D₂ D₃ : Type w} [Category.{z} D₀] [Category.{z} D₁]
  [Category.{z} D₂] [Category.{z} D₃]
  {a : C₀ ⥤ C₁} {b : C₁ ⥤ C₃} {c : C₀ ⥤ C₂} {d : C₂ ⥤ C₃}
  {P : D₀ ⥤ D₁} {M : D₁ ⥤ D₃} {Q : D₀ ⥤ D₂} {N : D₂ ⥤ D₃}
  {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}

/-- Lift an original square through the actual common-universe functors. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SmallModel/RouteRectangle.lean:31"
  "adaptation" "Original full rectangle, actual source transport and both normalized routes."]
def asSmallSquareIso (s : a ⋙ E₁ ≅ E₀ ⋙ P) :
    a ⋙ (E₁ ⋙ AsSmall.up.{z, w, 0}) ≅
      (E₀ ⋙ AsSmall.up.{z, w, 0}) ⋙ asSmallFunctor P :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight s AsSmall.up.{z, w, 0}

/-- The genuine up/down lift of the whole target input rectangle. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SmallModel/RouteRectangle.lean:37"
  "adaptation" "Original full rectangle, actual source transport and both normalized routes."]
def asSmallRectangleIso (r : P ⋙ M ≅ Q ⋙ N) :
    asSmallFunctor P ⋙ asSmallFunctor M ≅
      asSmallFunctor Q ⋙ asSmallFunctor N :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down.{z, w, 0} r) AsSmall.up.{z, w, 0}

private theorem route_inv_app
    (s : a ⋙ E₁ ≅ E₀ ⋙ P) (t : b ⋙ E₃ ≅ E₁ ⋙ M) (K : C₀) :
    (isoSquareRoute s t).inv.app K = M.map (s.inv.app K) ≫ t.inv.app (a.obj K) := by
  simp only [isoSquareRoute, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id]

private theorem square_inv_app_down (s : a ⋙ E₁ ≅ E₀ ⋙ P) (K : C₀) :
    ((asSmallSquareIso s).inv.app K).down = s.inv.app K := by
  change s.inv.app K ≫ 𝟙 _ = s.inv.app K
  exact Category.comp_id _

private theorem rectangle_hom_app_down (r : P ⋙ M ≅ Q ⋙ N) (K : AsSmall.{0} D₀) :
    ((asSmallRectangleIso r).hom.app K).down = r.hom.app (AsSmall.down.obj K) := rfl

private theorem smallFunctor_map_down {D E : Type w} [Category.{z} D] [Category.{z} E]
    (F : D ⥤ E) {X Y : AsSmall.{0} D} (f : X ⟶ Y) :
    ((asSmallFunctor F).map f).down = F.map f.down := rfl

/-- Actual common-universe transport preserves both complete independent square routes. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SmallModel/RouteRectangle.lean:63"
  "adaptation" "Original full rectangle, actual source transport and both normalized routes."]
theorem asSmallRouteRectangle
    (s : a ⋙ E₁ ≅ E₀ ⋙ P) (t : b ⋙ E₃ ≅ E₁ ⋙ M)
    (v : c ⋙ E₂ ≅ E₀ ⋙ Q) (w : d ⋙ E₃ ≅ E₂ ⋙ N)
    (r : P ⋙ M ≅ Q ⋙ N) (h : a ⋙ b = c ⋙ d)
    (hsq : whiskerLeft E₀ r.hom ≫ (isoSquareRoute v w).inv =
      (isoSquareRoute s t).inv ≫ eqToHom (congrArg (fun F => F ⋙ E₃) h)) :
    whiskerLeft (E₀ ⋙ AsSmall.up.{z, w, 0}) (asSmallRectangleIso r).hom ≫
        (isoSquareRoute (asSmallSquareIso v) (asSmallSquareIso w)).inv =
      (isoSquareRoute (asSmallSquareIso s) (asSmallSquareIso t)).inv ≫
        eqToHom (congrArg (fun F => F ⋙ (E₃ ⋙ AsSmall.up.{z, w, 0})) h) := by
  apply NatTrans.ext
  funext K
  apply ULift.ext
  have he := NatTrans.congr_app hsq K
  simp only [NatTrans.comp_app, route_inv_app, whiskerLeft_app, eqToHom_app] at he
  simp only [NatTrans.comp_app, whiskerLeft_app, route_inv_app, down_comp,
    rectangle_hom_app_down, smallFunctor_map_down, square_inv_app_down,
    Functor.comp_obj, eqToHom_app, eqToHom_down]
  change r.hom.app (E₀.obj K) ≫ N.map (v.inv.app K) ≫ w.inv.app (c.obj K) =
    (M.map (s.inv.app K) ≫ t.inv.app (a.obj K)) ≫
      eqToHom (congrArg (fun F : C₀ ⥤ C₃ => E₃.obj (F.obj K)) h)
  exact he

end CategoryTheory.Waldhausen
