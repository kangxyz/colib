/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModCorestriction

/-!
# Restriction followed by corestriction in all Ext degrees

The actual inverse-image/direct-image adjunction unit is natural on Ext. Combined with the
actual trace-degree formula this identifies corestriction after restriction, without a
projection-formula assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

attribute [local instance] finiteEtaleZModDirectImage_preservesFiniteColimits
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits
  comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) X)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) Y)]
  [EnoughInjectives (EtaleModules.{u, 0} (ZMod n) X)]

set_option maxHeartbeats 800000 in
-- Exact-functor comparison and the concrete sheaf adjunction require additional reduction budget.
/-- In every degree, restriction followed by the actual trace corestriction acts by degree. -/
theorem finiteEtaleZModCorestriction_restriction
    (A M : EtaleModules.{u, 0} (ZMod n) X) (p : ℕ) (e : Ext.{w} A M p)
    {d : ℕ} [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] :
    finiteEtaleZModCorestriction n g A M p
      (e.mapExactFunctor (etaleModuleInverseImage (ZMod n) g)) =
      e.comp (Ext.mk₀ (d • 𝟙 M)) (add_zero p) := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (etaleModuleInverseImageAdj (ZMod n) g).unit A p e
  rw [Stacks.ExtFunctorial.mapExactFunctor_id] at key
  change ((Ext.mk₀ _).comp
    ((e.mapExactFunctor (etaleModuleInverseImage (ZMod n) g)).mapExactFunctor
      (etaleModuleDirectImage (ZMod n) g)) (zero_add p)).comp _ (add_zero p) = _
  rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor, key,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    unit_comp_finiteEtaleZModTrace n g M (d := d)]

end Stacks.EtaleCohomology
