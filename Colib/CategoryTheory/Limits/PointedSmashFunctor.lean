/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmash

/-!
# Functoriality of the pointed smash quotient

The actual pointed smash pushout gives an endofunctor for a fixed right
factor. Changing that factor acts by the existing maps of the same
pushouts.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] [HasTerminal C]
  [HasBinaryProducts C] [HasBinaryCoproducts C] [HasPushouts C]

/-- Smash on the right with the specified pointed object. -/
def smashRightFunctor (Y : Under (⊤_ C)) : Under (⊤_ C) ⥤ Under (⊤_ C) where
  obj X := smash X Y
  map f := smashMap f (𝟙 Y)
  map_id X := smashMap_id X Y
  map_comp f g := by
    rw [smashMap_comp, Category.id_comp]

/-- Changing the right factor induces the actual maps of smash quotients. -/
def smashRightBifunctor : Under (⊤_ C) ⥤ (Under (⊤_ C) ⥤ Under (⊤_ C)) where
  obj := smashRightFunctor
  map g :=
    { app := fun X ↦ smashMap (𝟙 X) g
      naturality := fun _ _ f ↦ by
        change smashMap f (𝟙 _) ≫ smashMap (𝟙 _) g =
          smashMap (𝟙 _) g ≫ smashMap f (𝟙 _)
        simp only [smashMap_comp, Category.id_comp, Category.comp_id] }
  map_id Y := by
    apply NatTrans.ext
    funext X
    exact smashMap_id X Y
  map_comp f g := by
    apply NatTrans.ext
    funext X
    change smashMap (𝟙 X) (f ≫ g) = smashMap (𝟙 X) f ≫ smashMap (𝟙 X) g
    rw [smashMap_comp, Category.id_comp]

end CategoryTheory.Under
