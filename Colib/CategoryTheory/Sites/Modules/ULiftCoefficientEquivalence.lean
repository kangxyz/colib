/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.RootsOfUnityULiftModule
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Removing the coefficient universe lift

The equivalence acts on the actual coefficient objects and
uses the native restrictScalars equivalence, not an arbitrary abelian replacement.
-/

@[expose] public noncomputable section
open CategoryTheory
universe s v u
namespace Stacks.Cohomology.ZModSheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- Native module scalar equivalence with the precise section universe. -/
abbrev removeULiftModuleEquivalence (_J : GrothendieckTopology C) :
    ModuleCat.{max u v} (ULift.{s} (ZMod n)) ≌ ModuleCat.{max u v} (ZMod n) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{s} (ZMod n) ≃+* ZMod n).symm

/-- Restricting through the inverse ring equivalence removes the scalar lift. -/
abbrev removeULiftCoefficients :
    Sheaf J (ModuleCat.{max u v} (ULift.{s} (ZMod n))) ⥤
      Sheaf J (ModuleCat.{max u v} (ZMod n)) :=
  sheafCompose J (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{s} (ZMod n) ≃+* ZMod n).symm.toRingHom)

/-- Restoring the lifted scalar presentation. -/
abbrev restoreULiftCoefficients :
    Sheaf J (ModuleCat.{max u v} (ZMod n)) ⥤
      Sheaf J (ModuleCat.{max u v} (ULift.{s} (ZMod n))) :=
  sheafCompose J (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{s} (ZMod n) ≃+* ZMod n).toRingHom)

/-- The inverse scalar restriction equivalence, on actual sheaves. -/
def removeULiftCoefficientEquivalence :
    Sheaf J (ModuleCat.{max u v} (ULift.{s} (ZMod n))) ≌
      Sheaf J (ModuleCat.{max u v} (ZMod n)) :=
  CategoryTheory.Equivalence.mk (removeULiftCoefficients J n) (restoreULiftCoefficients J n)
  (NatIso.ofComponents (fun M =>
    (sheafToPresheaf J _).preimageIso
      ((Functor.rightUnitor M.obj).symm ≪≫
        Functor.isoWhiskerLeft M.obj
          (removeULiftModuleEquivalence (n := n) J).unitIso ≪≫
        (Functor.associator _ _ _).symm)) (by
    intro M N f
    apply (sheafToPresheaf J _).map_injective
    simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage]
    ext U x
    rfl))
  (NatIso.ofComponents (fun M =>
    (sheafToPresheaf J _).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft M.obj
          (removeULiftModuleEquivalence (n := n) J).counitIso ≪≫
        Functor.rightUnitor M.obj)) (by
    intro M N f
    apply (sheafToPresheaf J _).map_injective
    simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage]
    ext U x
    rfl))

end Stacks.Cohomology.ZModSheaf
