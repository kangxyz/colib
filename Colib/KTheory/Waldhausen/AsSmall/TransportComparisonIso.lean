/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.AsSmall.ComparisonIso
public import Colib.CategoryTheory.Functor.TransportIso

/-!
# Components of transported small-model comparisons

The endpoint equality morphisms and the original component are computed together in
abstract categories. This avoids unfolding a concrete geometric category to project a
transported comparison.
-/
@[expose] public noncomputable section

namespace CategoryTheory.Waldhausen

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- The transported composition component retains both canonical endpoint transports. -/
theorem asSmallCompositionIso_transport_hom_app
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G)
    {F₀ G₀ : AsSmall.{0} C ⥤ AsSmall.{0} E}
    (hF : F₀ = asSmallFunctor H)
    (hG : G₀ = asSmallFunctor F ⋙ asSmallFunctor G) (x : AsSmall.{0} C) :
    (Functor.transportIso hF hG (asSmallCompositionIso F G H i)).hom.app x =
      eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} E => K.obj x) hF) ≫
        (AsSmall.up : E ⥤ AsSmall.{0} E).map (i.hom.app (AsSmall.down.obj x)) ≫
          eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} E => K.obj x) hG.symm) := by
  rw [Functor.transportIso_hom_app, asSmallCompositionIso_hom_app]
  congr 2

/-- The transported unit component retains both canonical endpoint transports. -/
theorem asSmallIdentityIso_transport_hom_app
    (F : C ⥤ C) (i : F ≅ 𝟭 C)
    {F₀ G₀ : AsSmall.{0} C ⥤ AsSmall.{0} C}
    (hF : F₀ = asSmallFunctor F) (hG : G₀ = 𝟭 (AsSmall.{0} C)) (x : AsSmall.{0} C) :
    (Functor.transportIso hF hG (asSmallIdentityIso F i)).hom.app x =
      eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} C => K.obj x) hF) ≫
        (AsSmall.up : C ⥤ AsSmall.{0} C).map (i.hom.app (AsSmall.down.obj x)) ≫
          eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} C => K.obj x) hG.symm) := by
  rw [Functor.transportIso_hom_app, asSmallIdentityIso_hom_app]
  congr 2

end CategoryTheory.Waldhausen
