/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.TorsionComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules

/-!
# Constant coefficient sheaf models

The original constant-ring module model is equivalent to module-valued sheaves.
This is an equivalence of abelian categories, not fullness of derived forgetful functors.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t s v u

namespace Stacks.Cohomology.ZModSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
variable [HasSheafify J CommRingCat.{s}]
  [J.WEqualsLocallyBijective CommRingCat.{s}]
  [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n))) AddCommGrpCat.{t})]

/-- The original constant coefficient ring model as module-valued sheaves. -/
def zmodModuleSheafEquivalence :
    SheafOfModules.{t} (zmodRingSheaf.{s} J n) ≌
      Sheaf J (ModuleCat.{t} (ULift.{s} (ZMod n))) := by
  let α : Stacks.PresheafOfModules.constRing (C := C) (ULift.{s} (ZMod n)) ⟶
      (zmodRingSheaf.{s} J n).obj := zmodRingMap.{s} J n
  letI : Presheaf.IsLocallyInjective J α := zmodRingMap_isLocallyInjective.{s} J n
  letI : Presheaf.IsLocallySurjective J α := zmodRingMap_isLocallySurjective.{s} J n
  exact Stacks.ConstantRingModules.moduleSheafEquivalence _ J α


/-- Reading the original coefficient model as module sheaves preserves its abelian sheaf. -/
def zmodModuleSheafForgetIso :
    (zmodModuleSheafEquivalence.{t, s} J n).functor ⋙
        sheafCompose J (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n))) AddCommGrpCat.{t}) ≅
      SheafOfModules.toSheaf (zmodRingSheaf.{s} J n) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end Stacks.Cohomology.ZModSheaf
