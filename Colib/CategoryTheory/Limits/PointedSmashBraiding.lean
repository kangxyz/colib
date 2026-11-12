/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmashFunctor

/-!
# Swapping the factors of a pointed smash

The braiding of the binary product interchanges the two collapsed axes.
It induces a natural isomorphism on the original smash quotients and
compares suspension by a fixed object on the left and on the right.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] [HasTerminal C]
  [HasBinaryProducts C] [HasBinaryCoproducts C]

private theorem axesToProduct_braiding (X Y : Under (⊤_ C)) :
    axesToProduct X Y ≫ (prod.braiding X.right Y.right).hom =
      (coprod.braiding X.right Y.right).hom ≫ axesToProduct Y X := by
  apply coprod.hom_ext <;> apply prod.hom_ext <;>
    simp [axesToProduct, prod.braiding, coprod.braiding]

variable [HasPushouts C]

private def swapSmash (X Y : Under (⊤_ C)) : smash X Y ⟶ smash Y X :=
  Under.homMk (pushout.desc
    ((prod.braiding X.right Y.right).hom ≫ toSmash Y X) (smash Y X).hom (by
      rw [← Category.assoc, axesToProduct_braiding, Category.assoc,
        axesToProduct_toSmash, terminal.comp_from_assoc]))
    (pushout.inr_desc _ _ _)

@[reassoc]
private theorem toSmash_swapSmash (X Y : Under (⊤_ C)) :
    toSmash X Y ≫ (swapSmash X Y).right =
      (prod.braiding X.right Y.right).hom ≫ toSmash Y X :=
  pushout.inl_desc _ _ _

/-- Swap the factors by the native product braiding on the original quotient. -/
@[no_expose]
def smashBraiding (X Y : Under (⊤_ C)) : smash X Y ≅ smash Y X where
  hom := swapSmash X Y
  inv := swapSmash Y X
  hom_inv_id := by
    apply smash_hom_ext
    rw [Under.comp_right, toSmash_swapSmash_assoc, toSmash_swapSmash,
      prod.symmetry_assoc, Under.id_right, Category.comp_id]
  inv_hom_id := by
    apply smash_hom_ext
    rw [Under.comp_right, toSmash_swapSmash_assoc, toSmash_swapSmash,
      prod.symmetry_assoc, Under.id_right, Category.comp_id]

@[reassoc]
theorem toSmash_smashBraiding_hom (X Y : Under (⊤_ C)) :
    toSmash X Y ≫ (smashBraiding X Y).hom.right =
      (prod.braiding X.right Y.right).hom ≫ toSmash Y X :=
  toSmash_swapSmash X Y

/-- Swapping the smash factors carries their original maps to the reverse order. -/
@[reassoc]
theorem smashMap_smashBraiding_hom {X X' Y Y' : Under (⊤_ C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    smashMap f g ≫ (smashBraiding X' Y').hom =
      (smashBraiding X Y).hom ≫ smashMap g f := by
  apply smash_hom_ext
  simp only [Under.comp_right, toSmash_smashMap_assoc, toSmash_smashBraiding_hom_assoc,
    toSmash_smashBraiding_hom, toSmash_smashMap, braid_natural_assoc]

/-- Smash on the left with the specified pointed object. -/
def smashLeftFunctor (Y : Under (⊤_ C)) : Under (⊤_ C) ⥤ Under (⊤_ C) where
  obj X := smash Y X
  map f := smashMap (𝟙 Y) f
  map_id X := smashMap_id Y X
  map_comp f g := by rw [smashMap_comp, Category.id_comp]

/-- The left and right smash functors are compared by the original swap. -/
def smashRightIsoLeft (Y : Under (⊤_ C)) : smashRightFunctor Y ≅ smashLeftFunctor Y :=
  NatIso.ofComponents (fun X ↦ smashBraiding X Y) fun f ↦
    smashMap_smashBraiding_hom f (𝟙 Y)

end CategoryTheory.Under
