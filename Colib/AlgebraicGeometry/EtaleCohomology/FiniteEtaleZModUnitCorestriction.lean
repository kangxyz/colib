/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModCorestrictionDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct

/-!
# Corestriction with the original monoidal unit as source

The inverse image of the monoidal unit is canonically isomorphic to the original source
unit. Transport through this native comparison makes the trace corestriction applicable
to ordinary cup-product classes, without replacing their source object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal
  finiteEtaleZModDirectImage_preservesFiniteColimits
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) X)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) Y)]

/-- The actual trace corestriction on classes whose source is the original monoidal unit. -/
def finiteEtaleZModUnitCorestriction (M : EtaleModules.{u, 0} (ZMod n) X) (p : ℕ) :
    Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod n) Y))
      ((etaleModuleInverseImage (ZMod n) g).obj M) p →+
      Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod n) X)) M p where
  toFun e := finiteEtaleZModCorestriction n g _ M p
    ((Ext.mk₀ (Functor.OplaxMonoidal.η (etaleModuleInverseImage (ZMod n) g))).comp
      e (zero_add p))
  map_zero' := by simp
  map_add' e e' := by simp [Ext.comp_add]

/-- Native restriction of a unit-source class followed by corestriction acts by degree. -/
theorem finiteEtaleZModUnitCorestriction_mapUnit
    [EnoughInjectives (EtaleModules.{u, 0} (ZMod n) X)]
    (M : EtaleModules.{u, 0} (ZMod n) X) (p : ℕ)
    (e : Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod n) X)) M p)
    {d : ℕ} [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] :
    finiteEtaleZModUnitCorestriction n g M p
      (Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod n) g) e) =
      e.comp (Ext.mk₀ (d • 𝟙 M)) (add_zero p) := by
  change finiteEtaleZModCorestriction n g _ M p
    ((Ext.mk₀ (Functor.OplaxMonoidal.η (etaleModuleInverseImage (ZMod n) g))).comp
      ((Ext.mk₀ (Functor.LaxMonoidal.ε (etaleModuleInverseImage (ZMod n) g))).comp
        (e.mapExactFunctor (etaleModuleInverseImage (ZMod n) g)) (zero_add p))
      (zero_add p)) = _
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  simp only [Functor.Monoidal.η_ε, Ext.mk₀_id_comp]
  exact finiteEtaleZModCorestriction_restriction n g _ M p e

end Stacks.EtaleCohomology
