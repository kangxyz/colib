/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.AsSmall.TransportComparisonIso
public import Colib.KTheory.Waldhausen.Iterated.SmallModelWhiskering

/-!
# Transported comparisons in the native small-model category

The native model carrier is the actual `AsSmall` carrier, not a second lift. The
constructors and their component formulas retain the same model category parameters,
so concrete geometric uses do not have to identify independently elaborated category
instances. All endpoint equality morphisms and original comparison components remain.
-/
@[expose] public noncomputable section

namespace CategoryTheory.Waldhausen.IteratedS

universe u v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- The original composition comparison with its exact native-model endpoint transports. -/
def modelAsSmallCompositionIso
    (W : Structure C) (V : Structure E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G)
    {F₀ G₀ : @Functor (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category
      (asSmallCategory V).obj.Obj (asSmallCategory V).obj.category}
    (hF : F₀ = asSmallFunctor H)
    (hG : G₀ = asSmallFunctor F ⋙ asSmallFunctor G) : F₀ ≅ G₀ :=
  Functor.transportIso hF hG (asSmallCompositionIso F G H i)

/-- The constructor keeps the original lifted constraint and both equality morphisms. -/
theorem modelAsSmallCompositionIso_eq
    (W : Structure C) (V : Structure E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G)
    {F₀ G₀ : @Functor (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category
      (asSmallCategory V).obj.Obj (asSmallCategory V).obj.category}
    (hF : F₀ = asSmallFunctor H)
    (hG : G₀ = asSmallFunctor F ⋙ asSmallFunctor G) :
    modelAsSmallCompositionIso W V F G H i hF hG =
      Functor.transportIso hF hG (asSmallCompositionIso F G H i) := rfl

/-- The native-model composition component, without discarding endpoint transports. -/
theorem modelAsSmallCompositionIso_hom_app
    (W : Structure C) (V : Structure E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G)
    {F₀ G₀ : @Functor (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category
      (asSmallCategory V).obj.Obj (asSmallCategory V).obj.category}
    (hF : F₀ = asSmallFunctor H)
    (hG : G₀ = asSmallFunctor F ⋙ asSmallFunctor G) (x : AsSmall.{0} C) :
    (modelAsSmallCompositionIso W V F G H i hF hG).hom.app x =
      eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} E => K.obj x) hF) ≫
        (AsSmall.up : E ⥤ AsSmall.{0} E).map (i.hom.app (AsSmall.down.obj x)) ≫
          eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} E => K.obj x) hG.symm) := by
  unfold modelAsSmallCompositionIso
  exact asSmallCompositionIso_transport_hom_app F G H i hF hG x

/-- The original unit comparison with its exact native-model endpoint transports. -/
def modelAsSmallIdentityIso
    (W : Structure C) (F : C ⥤ C) (i : F ≅ 𝟭 C)
    {F₀ G₀ : @Functor (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category
      (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category}
    (hF : F₀ = asSmallFunctor F) (hG : G₀ = 𝟭 (AsSmall.{0} C)) : F₀ ≅ G₀ :=
  Functor.transportIso hF hG (asSmallIdentityIso F i)

/-- The unit constructor keeps the original lifted constraint and both equality morphisms. -/
theorem modelAsSmallIdentityIso_eq
    (W : Structure C) (F : C ⥤ C) (i : F ≅ 𝟭 C)
    {F₀ G₀ : @Functor (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category
      (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category}
    (hF : F₀ = asSmallFunctor F) (hG : G₀ = 𝟭 (AsSmall.{0} C)) :
    modelAsSmallIdentityIso W F i hF hG =
      Functor.transportIso hF hG (asSmallIdentityIso F i) := rfl

/-- The native-model unit component, without discarding endpoint transports. -/
theorem modelAsSmallIdentityIso_hom_app
    (W : Structure C) (F : C ⥤ C) (i : F ≅ 𝟭 C)
    {F₀ G₀ : @Functor (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category
      (asSmallCategory W).obj.Obj (asSmallCategory W).obj.category}
    (hF : F₀ = asSmallFunctor F) (hG : G₀ = 𝟭 (AsSmall.{0} C)) (x : AsSmall.{0} C) :
    (modelAsSmallIdentityIso W F i hF hG).hom.app x =
      eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} C => K.obj x) hF) ≫
        (AsSmall.up : C ⥤ AsSmall.{0} C).map (i.hom.app (AsSmall.down.obj x)) ≫
          eqToHom (congrArg (fun K : AsSmall.{0} C ⥤ AsSmall.{0} C => K.obj x) hG.symm) := by
  unfold modelAsSmallIdentityIso
  exact asSmallIdentityIso_transport_hom_app F i hF hG x

end CategoryTheory.Waldhausen.IteratedS
