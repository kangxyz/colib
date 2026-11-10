/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Waldhausen.AsSmall.Basic
/-!
# Actual AsSmall lifts of composition and identity comparisons

The existing Waldhausen small-model functor lifts the original natural isomorphisms.
All up/down cancellation is performed in abstract categories, with independent object
and hom universes. These are comparisons of the original functors, not a second lift.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen
universe u v
namespace CategoryTheory.Waldhausen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- Lift an original composition comparison to the actual small-model functors. -/
def asSmallCompositionIso
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G) :
    asSmallFunctor H ≅ asSmallFunctor F ⋙ asSmallFunctor G :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight i AsSmall.up)

/-- The lifted composition comparison is the original doubly whiskered transformation. -/
theorem asSmallCompositionIso_hom
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G) :
    (asSmallCompositionIso F G H i).hom =
      whiskerLeft AsSmall.down (whiskerRight i.hom AsSmall.up) := rfl

/-- Every lifted composition component is the actual up-image of the original component. -/
theorem asSmallCompositionIso_hom_app
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (i : H ≅ F ⋙ G)
    (x : AsSmall.{0} C) :
    (asSmallCompositionIso F G H i).hom.app x =
      (AsSmall.up : E ⥤ AsSmall.{0} E).map (i.hom.app (AsSmall.down.obj x)) := rfl

/-- Lift an original identity comparison to the actual small-model identity. -/
def asSmallIdentityIso (F : C ⥤ C) (i : F ≅ 𝟭 C) :
    asSmallFunctor F ≅ 𝟭 (AsSmall.{0} C) :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight i AsSmall.up)

/-- The lifted identity comparison is the original doubly whiskered transformation. -/
theorem asSmallIdentityIso_hom (F : C ⥤ C) (i : F ≅ 𝟭 C) :
    (asSmallIdentityIso F i).hom =
      whiskerLeft AsSmall.down (whiskerRight i.hom AsSmall.up) := rfl

/-- Every lifted identity component is the actual up-image of the original component. -/
theorem asSmallIdentityIso_hom_app (F : C ⥤ C) (i : F ≅ 𝟭 C)
    (x : AsSmall.{0} C) :
    (asSmallIdentityIso F i).hom.app x =
      (AsSmall.up : C ⥤ AsSmall.{0} C).map (i.hom.app (AsSmall.down.obj x)) := rfl
end CategoryTheory.Waldhausen
