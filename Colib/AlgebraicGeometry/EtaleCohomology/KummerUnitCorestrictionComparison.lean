/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCorestrictionSource
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModUnitCorestriction

/-! # Original unit-source and constant-source trace corestrictions

Naturality of the native adjunction unit compares the two
source conventions; neither corestriction definition is replaced.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry
universe w u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal
  finiteEtaleZModDirectImage_preservesFiniteColimits
variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) X)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod n) Y)]

set_option backward.isDefEq.respectTransparency false in
/-- Source naturality of the actual finite étale trace corestriction. -/
theorem kummerCorestriction_source_naturality
    {A A' : EtaleModules.{u, 0} (ZMod n) X} (u : A ⟶ A')
    (M : EtaleModules.{u, 0} (ZMod n) X) (q : ℕ)
    (e : Ext.{w} ((etaleModuleInverseImage (ZMod n) g).obj A')
      ((etaleModuleInverseImage (ZMod n) g).obj M) q) :
    finiteEtaleZModCorestriction n g A M q
      ((Ext.mk₀ ((etaleModuleInverseImage (ZMod n) g).map u)).comp e (zero_add q)) =
    (Ext.mk₀ u).comp (finiteEtaleZModCorestriction n g A' M q e) (zero_add q) := by
  have hn := (etaleModuleInverseImageAdj (ZMod n) g).unit.naturality u
  change u ≫ (etaleModuleInverseImageAdj (ZMod n) g).unit.app A' =
    (etaleModuleInverseImageAdj (ZMod n) g).unit.app A ≫
      (etaleModuleDirectImage (ZMod n) g).map
        ((etaleModuleInverseImage (ZMod n) g).map u) at hn
  simp only [finiteEtaleZModCorestriction, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, ← hn]
  simp only [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual unit-source trace equals the actual constant-source trace,
transported through the original Kummer source isomorphism. -/
theorem kummerUnitCorestrictionComparison
    (M : EtaleModules.{u, 0} (ZMod n) X) (q : ℕ)
    (e : Ext.{w}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) Y.smallEtaleTopology)
      ((etaleModuleInverseImage (ZMod n) g).obj M) q) :
    finiteEtaleZModUnitCorestriction n g M q
      ((Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom).comp e (zero_add q)) =
    (Ext.mk₀ (etaleModuleUnitIsoConstant (X := X) n).hom).comp
      (finiteEtaleZModCorestriction n g
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology)
        M q ((Ext.mk₀ ((etaleModuleInverseImageConstantIso (ZMod n) g).hom.app
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))).comp e (zero_add q)))
      (zero_add q) := by
  change finiteEtaleZModCorestriction n g _ M q
    ((Ext.mk₀ (Functor.OplaxMonoidal.η (etaleModuleInverseImage (ZMod n) g))).comp
      ((Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom).comp e (zero_add q))
      (zero_add q)) = _
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  erw [← kummerCorestrictionSource_unitIso_square g n]
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  exact kummerCorestriction_source_naturality n g
    (etaleModuleUnitIsoConstant (X := X) n).hom M q _

end Stacks.EtaleCohomology
end
