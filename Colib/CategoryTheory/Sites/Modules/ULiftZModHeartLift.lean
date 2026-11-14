/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.ZModSheafModel
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Linear lifting in the coefficient heart

Fullness here is strictly in module/sheaf categories, never
in their derived categories. This handles the literal ULift coefficient model.
-/

@[expose] public noncomputable section
open CategoryTheory
universe t s v u

namespace Stacks.Cohomology.ZModSheaf

/-- Every additive morphism between the literal lifted coefficient modules is linear. -/
def uliftZModForgetFullyFaithful (n : ℕ) :
    (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n))) AddCommGrpCat.{t}).FullyFaithful where
  preimage {X Y} f := ModuleCat.ofHom
    { f.hom with
      map_smul' := fun r x => map_smul_of_isAddHom (A := X) (B := Y) f.hom r x }
  map_preimage _ := rfl
  preimage_map _ := rfl

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n))) AddCommGrpCat.{t})]

/-- Fullness of forgetting the literal lifted coefficient SHEAF structure. -/
def uliftZModSheafForgetFullyFaithful :
    (sheafCompose J
      (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n))) AddCommGrpCat.{t})).FullyFaithful :=
  fullyFaithfulSheafCompose J (uliftZModForgetFullyFaithful.{t, s} n)

end Stacks.Cohomology.ZModSheaf
