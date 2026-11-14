/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModTrace
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Corestriction from the actual finite étale trace

The exact direct image and the original inverse-image adjunction transport Ext classes,
then the actual finite étale trace returns to the original coefficient. The source here
is an inverse image of the specified object, so no replacement of the tensor unit is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]

omit [Etale g] in
/-- Finite direct image on Z/n-module sheaves preserves finite colimits, as detected by
fully faithful forgetting to the exact abelian direct image. -/
theorem finiteEtaleZModDirectImage_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod n) g) := by
  have : PreservesFiniteColimits
      (etaleModuleDirectImage.{u, 0} (ZMod n) g ⋙ etaleModuleForgetAb (ZMod n) X) := by
    change PreservesFiniteColimits
      (etaleModuleForgetAb (ZMod n) Y ⋙ smallEtalePushforwardAb g)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves
    (etaleModuleDirectImage.{u, 0} (ZMod n) g) (etaleModuleForgetAb (ZMod n) X)

attribute [local instance] finiteEtaleZModDirectImage_preservesFiniteColimits

variable [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) X)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) Y)]

/-- Corestriction defined using the original inverse-image unit, exact direct image,
and the actual finite étale module trace. -/
def finiteEtaleZModCorestriction (A M : EtaleModules.{u, 0} (ZMod n) X) (p : ℕ) :
    Ext.{w} ((etaleModuleInverseImage (ZMod n) g).obj A)
      ((etaleModuleInverseImage (ZMod n) g).obj M) p →+ Ext.{w} A M p where
  toFun e := ((Ext.mk₀ ((etaleModuleInverseImageAdj (ZMod n) g).unit.app A)).comp
    (e.mapExactFunctor (etaleModuleDirectImage (ZMod n) g)) (zero_add p)).comp
      (Ext.mk₀ (finiteEtaleZModTrace n g M)) (add_zero p)
  map_zero' := by simp
  map_add' e e' := by simp [Ext.comp_add, Ext.add_comp]

/-- In degree zero this corestriction is exactly the original unit, direct image and trace. -/
theorem finiteEtaleZModCorestriction_mk₀ (A M : EtaleModules.{u, 0} (ZMod n) X)
    (f : (etaleModuleInverseImage (ZMod n) g).obj A ⟶
      (etaleModuleInverseImage (ZMod n) g).obj M) :
    finiteEtaleZModCorestriction n g A M 0 (Ext.mk₀ f) =
      Ext.mk₀ ((etaleModuleInverseImageAdj (ZMod n) g).unit.app A ≫
        (etaleModuleDirectImage (ZMod n) g).map f ≫ finiteEtaleZModTrace n g M) := by
  simp [finiteEtaleZModCorestriction, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- On degree-zero restricted morphisms the actual corestriction is multiplication by degree. -/
theorem finiteEtaleZModCorestriction_map_mk₀
    (A M : EtaleModules.{u, 0} (ZMod n) X) (f : A ⟶ M)
    {d : ℕ} [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] :
    finiteEtaleZModCorestriction n g A M 0
      (Ext.mk₀ ((etaleModuleInverseImage (ZMod n) g).map f)) = Ext.mk₀ (d • f) := by
  rw [finiteEtaleZModCorestriction_mk₀]
  congr 1
  have h := (etaleModuleInverseImageAdj (ZMod n) g).unit.naturality f
  change f ≫ _ = _ ≫ (etaleModuleDirectImage (ZMod n) g).map
    ((etaleModuleInverseImage (ZMod n) g).map f) at h
  rw [← Category.assoc, ← h, Category.assoc, unit_comp_finiteEtaleZModTrace n g M (d := d)]
  simp

end Stacks.EtaleCohomology
