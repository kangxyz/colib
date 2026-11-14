/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.ExtCupMonoidalAdjunction
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModProjectionFormula
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModUnitCorestriction

/-!
# Actual finite étale corestriction and Ext cup products

The exactness hypotheses on the three tensor-right functors
are explicit: these must be discharged for the actual coefficients in the application.
No projection square is assumed; the proof uses the verified native sheaf theorem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry
open Functor.LaxMonoidal
universe w u
namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal
  etaleModuleInverseImageSheafPullbackMonoidal
  finiteEtaleZModDirectImage_preservesFiniteColimits
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) X)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) Y)]

/-- The existing unit-source corestriction is the existing right-adjoint mapUnit
followed by the actual trace, not a replacement map. -/
theorem finiteEtaleZModUnitCorestriction_eq_mapUnit_trace
    (M : EtaleModules.{u, 0} (ZMod n) X) (p : ℕ)
    (b : Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod n) Y))
      ((etaleModuleInverseImage (ZMod n) g).obj M) p) :
    finiteEtaleZModUnitCorestriction n g M p b =
      (Stacks.ExtCup.mapUnit (etaleModuleDirectImage (ZMod n) g) b).comp
        (Ext.mk₀ (finiteEtaleZModTrace n g M)) (add_zero p) := by
  have := etaleModuleInverseImageAdj_native_isMonoidal (ZMod n) g
  simp only [finiteEtaleZModUnitCorestriction, finiteEtaleZModCorestriction,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Stacks.ExtCup.mapUnit]
  rw [← Adjunction.IsMonoidal.leftAdjoint_ε
    (adj := etaleModuleInverseImageAdj (ZMod n) g)]

/-- Projection formula for the original native restriction, actual corestriction,
and the existing Ext cup product, in arbitrary degrees. -/
theorem finiteEtaleZModUnitCorestriction_cup
    [EnoughInjectives (EtaleModules.{u, 0} (ZMod n) X)]
    [EnoughInjectives (EtaleModules.{u, 0} (ZMod n) Y)]
    (F G : EtaleModules.{u, 0} (ZMod n) X)
    [(MonoidalCategory.tensorRight G).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight G)]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight G)]
    [(MonoidalCategory.tensorRight ((etaleModuleInverseImage (ZMod n) g).obj G)).Additive]
    [PreservesFiniteLimits
      (MonoidalCategory.tensorRight ((etaleModuleInverseImage (ZMod n) g).obj G))]
    [PreservesFiniteColimits
      (MonoidalCategory.tensorRight ((etaleModuleInverseImage (ZMod n) g).obj G))]
    [(MonoidalCategory.tensorRight ((etaleModuleDirectImage (ZMod n) g).obj
      ((etaleModuleInverseImage (ZMod n) g).obj G))).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight ((etaleModuleDirectImage (ZMod n) g).obj
      ((etaleModuleInverseImage (ZMod n) g).obj G)))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight ((etaleModuleDirectImage (ZMod n) g).obj
      ((etaleModuleInverseImage (ZMod n) g).obj G)))]
    {i j k : ℕ} (h : j + i = k)
    (a : Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod n) X)) F i)
    (b : Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod n) Y))
      ((etaleModuleInverseImage (ZMod n) g).obj G) j) :
    finiteEtaleZModUnitCorestriction n g (F ⊗ G) k
      (Stacks.ExtCup.cup (μ (etaleModuleInverseImage (ZMod n) g) F G)
        (Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod n) g) a) b h) =
      Stacks.ExtCup.cup (𝟙 (F ⊗ G)) a
        (finiteEtaleZModUnitCorestriction n g G j b) h := by
  have := etaleModuleInverseImageAdj_native_isMonoidal (ZMod n) g
  rw [finiteEtaleZModUnitCorestriction_eq_mapUnit_trace,
    Stacks.ExtCup.mapUnit_cup,
    Colib.ExtCup.mapUnit_mapUnit (etaleModuleInverseImage (ZMod n) g)
      (etaleModuleDirectImage (ZMod n) g) (etaleModuleInverseImageAdj (ZMod n) g),
    Stacks.ExtCup.cup_comp_mk₀, Stacks.ExtCup.comp_mk₀_cup,
    finiteEtaleZModUnitCorestriction_eq_mapUnit_trace,
    Stacks.ExtCup.cup_comp_mk₀_right]
  congr 1
  have hp := finiteEtaleZModProjection_trace n g F G
  unfold finiteEtaleZModProjection at hp
  rw [Colib.ProjectionMap.projectionMap_eq_unit_tensorator] at hp
  simpa only [Category.assoc, Category.comp_id] using hp

end Stacks.EtaleCohomology
