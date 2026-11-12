/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.Algebra.Category.FGModuleCat.IsFG
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Restriction of scalars for finite modules

The literal Mathlib scalar-restriction functor preserves finite modules along a finite
ring homomorphism. Its exactness is inherited from the actual module functor.
-/
@[expose] public noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
namespace FGModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Restriction along a finite ring map, with its actual underlying module functor. -/
def finiteRestriction (f : R →+* S) (hf : f.Finite) :
    FGModuleCat.{w} S ⥤ FGModuleCat.{w} R :=
  (ModuleCat.isFG R).lift
    (forget₂ (FGModuleCat.{w} S) (ModuleCat.{w} S) ⋙ ModuleCat.restrictScalars f) (fun M ↦ by
      let := f.toAlgebra
      let N := (ModuleCat.restrictScalars f).obj M.obj
      have : Module.Finite S N := M.property
      have : Module.Finite R S := hf
      have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      exact Module.Finite.trans S N)

instance finiteRestriction_additive (f : R →+* S) (hf : f.Finite) :
    (finiteRestriction.{u, v, w} f hf).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; rfl

/-- Restriction retains its literal underlying-module functor. -/
theorem finiteRestriction_comp_forget (f : R →+* S) (hf : f.Finite) :
    finiteRestriction.{u, v, w} f hf ⋙ forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R) =
      forget₂ (FGModuleCat.{w} S) (ModuleCat.{w} S) ⋙ ModuleCat.restrictScalars f := rfl

instance finiteRestriction_preservesFiniteColimits (f : R →+* S) (hf : f.Finite) :
    PreservesFiniteColimits (finiteRestriction.{u, v, w} f hf) := by
  have : PreservesFiniteColimits
      (finiteRestriction f hf ⋙ forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)) := by
    rw [finiteRestriction_comp_forget]
    exact comp_preservesFiniteColimits
      (forget₂ (FGModuleCat.{w} S) (ModuleCat.{w} S)) (ModuleCat.restrictScalars f)
  exact preservesFiniteColimits_of_reflects_of_preserves (finiteRestriction f hf)
    (forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R))

variable [IsNoetherianRing R] [IsNoetherianRing S]
instance finiteRestriction_preservesFiniteLimits (f : R →+* S) (hf : f.Finite) :
    PreservesFiniteLimits (finiteRestriction.{u, v, w} f hf) := by
  have : PreservesFiniteLimits
      (finiteRestriction f hf ⋙ forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)) := by
    rw [finiteRestriction_comp_forget]
    exact comp_preservesFiniteLimits
      (forget₂ (FGModuleCat.{w} S) (ModuleCat.{w} S)) (ModuleCat.restrictScalars f)
  exact preservesFiniteLimits_of_reflects_of_preserves (finiteRestriction f hf)
    (forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R))

/-- The actual finite scalar restriction with the standard abelian exact structures. -/
def finiteRestrictionExact (f : R →+* S) (hf : f.Finite) :
    ExactFunctor (abelianExactStructure (FGModuleCat.{w} S))
      (abelianExactStructure (FGModuleCat.{w} R)) where
  toFunctor := finiteRestriction f hf
  map_conflation _ h := h.map_of_exact _
end FGModuleCat
