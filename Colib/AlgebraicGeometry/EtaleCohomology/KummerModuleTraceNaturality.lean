/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleTraceComparison
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerUnitCorestrictionComparison
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerAbelianTraceBoundary

/-! # Actual trace of the original module-valued Kummer class

The trace is the sectionwise native multiplicative trace;
the original constant-source and monoidal-unit-source Kummer classes are retained.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal
  Stacks.EtaleCohomology.finiteEtaleZModDirectImage_preservesFiniteColimits
namespace Stacks.Kummer
open Stacks.EtaleCohomology
variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]
  (n : ℕ) [NeZero n] (hX : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option backward.isDefEq.respectTransparency false in
/-- Actual constant-source corestriction of the original module Kummer class
is the original class of the native multiplicative trace of its unit. -/
theorem kummerModuleTraceNaturality_class (t : Γ(Y, ⊤)ˣ) :
    finiteEtaleZModCorestriction n g
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology)
      (rootsOfUnityModule.{u, 0} X n) 1
      (((Ext.mk₀ ((etaleModuleInverseImageConstantIso (ZMod n) g).hom.app
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))).comp
          (kummerModuleClassModuloPowers Y n (isUnit_natCast_of_hom g hX)
            (QuotientAddGroup.mk (Additive.ofMul t))) (zero_add 1)).comp
          (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).inv) (add_zero 1)) =
    kummerModuleClassModuloPowers X n hX
      (QuotientAddGroup.mk (Additive.ofMul
        (finiteEtaleMultiplicativeTraceUnits g (Scheme.Etale.mk (𝟙 X)) t))) := by
  apply (rootsOfUnityModuleExtEquiv X n 1).injective
  rw [rootsOfUnityModuleExtEquiv_kummerModuleClass_mk]
  change extConstantAddEquivSheafH X _ 1 _ = _
  rw [kummerModuleTraceComparison]
  change kummerAbelianTraceCorestriction g n 1
      (rootsOfUnityModuleExtEquiv Y n 1
        (kummerModuleClassModuloPowers Y n (isUnit_natCast_of_hom g hX)
          (QuotientAddGroup.mk (Additive.ofMul t)))) = _
  rw [rootsOfUnityModuleExtEquiv_kummerModuleClass_mk,
    kummerAbelianTraceCorestriction_unitKummerClass]

set_option backward.isDefEq.respectTransparency false in
/-- Actual unit-source corestriction of the original Kummer unit class is the
original Kummer unit class of the sectionwise multiplicative trace. -/
theorem kummerModuleTraceNaturality_unitClass (t : Γ(Y, ⊤)ˣ) :
    finiteEtaleZModUnitCorestriction n g (rootsOfUnityModule.{u, 0} X n) 1
      ((kummerModuleUnitClass n (isUnit_natCast_of_hom g hX)
        (QuotientAddGroup.mk (Additive.ofMul t))).comp
          (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).inv) (add_zero 1)) =
    kummerModuleUnitClass n hX (QuotientAddGroup.mk (Additive.ofMul
      (finiteEtaleMultiplicativeTraceUnits g (Scheme.Etale.mk (𝟙 X)) t))) := by
  change finiteEtaleZModUnitCorestriction n g (rootsOfUnityModule.{u, 0} X n) 1
      (((Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom).comp
        (kummerModuleClassModuloPowers Y n (isUnit_natCast_of_hom g hX)
          (QuotientAddGroup.mk (Additive.ofMul t))) (zero_add 1)).comp
        (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).inv) (add_zero 1)) =
    (Ext.mk₀ (etaleModuleUnitIsoConstant (X := X) n).hom).comp
      (kummerModuleClassModuloPowers X n hX
        (QuotientAddGroup.mk (Additive.ofMul
          (finiteEtaleMultiplicativeTraceUnits g (Scheme.Etale.mk (𝟙 X)) t)))) (zero_add 1)
  rw [Ext.comp_assoc_of_third_deg_zero, kummerUnitCorestrictionComparison]
  rw [← Ext.comp_assoc_of_third_deg_zero, kummerModuleTraceNaturality_class]

end Stacks.Kummer
end
