/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# Original germs under the native comapped-point comparison

The comparison is the native adjunction mate. Its action on each original
marked germ is the actual continuous-site adjunction unit followed by the germ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v

namespace CategoryTheory.GrothendieckTopology.Point

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F]
  (hF : CoverPreserving J K F) [InitiallySmall (F ⋙ Φ.fiber).Elements]
  {A : Type*} [Category.{v} A] [HasProducts.{w} A]
  [Functor.IsContinuous F J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasColimitsOfSize.{w, w} A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The skyscraper adjunction unit evaluated at a marking is its original germ. -/
@[reassoc]
theorem skyscraperSheafAdjunction_unit_app_π
    (G : Sheaf K A) (U : D) (x : Φ.fiber.obj U) :
    (Φ.skyscraperSheafAdjunction.unit.app G).hom.app (op U) ≫ Pi.π _ x =
      Φ.toPresheafFiber U x G.obj := by
  rw [← Adjunction.homEquiv_id]
  erw [skyscraperSheafAdjunction_homEquiv_apply_hom,
    skyscraperPresheafHomEquiv_app_π, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The native comapped-point isomorphism preserves each marked germ through the actual unit. -/
@[reassoc]
theorem toPresheafFiber_sheafFiberComapIso_hom
    (G : Sheaf J A) (U : C) (x : Φ.fiber.obj (F.obj U)) :
    (Φ.comap F hF).toPresheafFiber U x G.obj ≫
        (Φ.sheafFiberComapIso F hF A).hom.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op U) ≫
        Φ.toPresheafFiber (F.obj U) x ((F.sheafPullback A J K).obj G).obj := by
  have h := unit_conjugateEquiv_symm
    ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    (Φ.comap F hF).skyscraperSheafAdjunction
    (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom G
  have h' := congrArg (fun k ↦ k.hom.app (op U) ≫ Pi.π _ x) h
  simp only [skyscraperSheafFunctorCompSheafPushforwardContinuous, Iso.refl_hom,
    NatTrans.id_app, Adjunction.comp_unit_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h'
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.assoc] at h'
  erw [Category.id_comp] at h'
  change
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op U) ≫
      ((Φ.skyscraperSheafAdjunction.unit.app _).hom.app (op (F.obj U)) ≫ Pi.π _ x) =
    ((Φ.comap F hF).skyscraperSheafAdjunction.unit.app G).hom.app (op U) ≫
      (((Φ.comap F hF).skyscraperSheafFunctor.map
        ((Φ.sheafFiberComapIso F hF A).hom.app G)).hom.app (op U) ≫ Pi.π _ x) at h'
  simp only [skyscraperSheafFunctor_map_hom, skyscraperPresheafFunctor_map_app,
    skyscraperSheafAdjunction_unit_app_π] at h'
  erw [Pi.map_π] at h'
  rw [← Category.assoc] at h'
  erw [skyscraperSheafAdjunction_unit_app_π] at h'
  exact h'.symm

end CategoryTheory.GrothendieckTopology.Point
