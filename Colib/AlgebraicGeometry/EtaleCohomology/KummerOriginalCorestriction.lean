/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalExtComparison
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerPushforwardForget
public import Colib.Util.References

/-! # The original Kummer comparison applied to finite étale corestriction

Read the actual trace corestriction through the original derived comparison as
an explicit abelian Ext composite. The integral constant-source map is retained:
forgetting module sheaves alone is not asserted to induce an Ext equivalence.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard
namespace Stacks.EtaleCohomology

attribute [colib_tag "COL-1227"] kummerOriginalComparison_eq_extForget
variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
attribute [local instance] finiteEtaleZModDirectImage_preservesFiniteColimits
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The actual original comparison sends trace corestriction to the explicit
constant-source, adjunction-unit, direct-image and native-trace composite. -/
theorem kummerOriginalComparison_corestriction
    (M : EtaleModules.{u, 0} (ZMod n) X) (q : ℕ)
    (e : Ext.{u + 1} ((etaleModuleInverseImage (ZMod n) g).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
        X.smallEtaleTopology)) ((etaleModuleInverseImage (ZMod n) g).obj M) q) :
    extConstantAddEquivSheafH X M q
      (finiteEtaleZModCorestriction n g _ M q e) =
    let A := Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
      X.smallEtaleTopology
    (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X)).comp
      (((Ext.mk₀ ((smallEtaleAdjunctionAb g).unit.app
          ((etaleModuleForgetAb (ZMod n) X).obj A) ≫
        (smallEtalePushforwardAb g).map
          ((traceForgetPullbackAbIso (ZMod n) g).hom.app A))).comp
        ((e.mapExactFunctor (etaleModuleForgetAb (ZMod n) Y)).mapExactFunctor
          (smallEtalePushforwardAb g)) (zero_add q)).comp
        (Ext.mk₀ ((smallEtalePushforwardAb g).map
          ((traceForgetPullbackAbIso (ZMod n) g).inv.app M) ≫
          finiteEtaleTraceOnPullbackAb g ((etaleModuleForgetAb (ZMod n) X).obj M)))
          (add_zero q)) (zero_add q) := by
  rw [kummerOriginalComparison_eq_extForget, extForgetSheafH_apply]
  exact congrArg
    (fun z => (Ext.mk₀ (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X)).comp
      z (zero_add q)) (finiteEtaleZModCorestriction_forgetExt n g _ M q e)

end Stacks.EtaleCohomology
end
