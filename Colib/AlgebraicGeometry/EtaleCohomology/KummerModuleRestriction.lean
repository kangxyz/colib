/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOrdinaryRestriction
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerOriginalExtFunctoriality
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerCorestrictionSource
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerRootsOfUnityTraceCompatibility

/-! # Restriction of the original module-valued Kummer classes

The original Kummer quotient and unit-source classes are retained.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory AlgebraicGeometry
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits
namespace Stacks.Kummer
open Stacks.EtaleCohomology
variable {X Y : Scheme.{u}} (g : Y ⟶ X)
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

-- Keep the bundled-map/Ext conversion small and independent of a concrete Kummer class.
set_option maxRecDepth 4096 in
omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
private theorem comparison_postcomp {Λ : Type} [CommRing Λ]
    {M M' : EtaleModules.{u, 0} Λ Y} (f : M ⟶ M') (q : ℕ)
    (x : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology) M q) :
    extConstantAddEquivSheafH Y M' q (x.comp (Ext.mk₀ f) (add_zero q)) =
      Sheaf.H.map ((etaleModuleUnderlyingAbelian Y Λ).map f) q
        (extConstantAddEquivSheafH Y M q x) := by
  exact kummerExtConstantAddEquivSheafH_naturality Y f q x

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
private theorem cohomologyMap_postcomp
    {A B C : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (alpha : A ⟶ B) (psi : B ⟶ C) (q : ℕ) (z : Sheaf.H.{u + 1} A q) :
    Sheaf.H.map psi q (z.comp (Ext.mk₀ alpha) (add_zero q)) =
      Sheaf.H.map (alpha ≫ psi) q z := by
  simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

variable (n : ℕ) [NeZero n] (hX : IsUnit (n : Γ(X, ⊤)))

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the original module Kummer class, with its actual roots comparison. -/
theorem kummerModuleRestriction_class (a : (Γ(X, ⊤))ˣ) :
    (etaleModuleExtRestriction (ZMod n) g (rootsOfUnityModule.{u, 0} X n) 1
      (kummerModuleClassModuloPowers X n hX
        (QuotientAddGroup.mk (Additive.ofMul a)))).comp
      (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).hom) (add_zero 1) =
    kummerModuleClassModuloPowers Y n (isUnit_natCast_of_hom g hX)
      (QuotientAddGroup.mk (Additive.ofMul (Units.map g.appTop.hom a))) := by
  apply (rootsOfUnityModuleExtEquiv Y n 1).injective
  change extConstantAddEquivSheafH Y _ 1 _ =
    extConstantAddEquivSheafH Y _ 1 _
  have hc := comparison_postcomp
    (rootsOfUnityModuleInverseImageIso g n hX).hom 1
    (etaleModuleExtRestriction (ZMod n) g (rootsOfUnityModule.{u, 0} X n) 1
      (kummerModuleClassModuloPowers X n hX
        (QuotientAddGroup.mk (Additive.ofMul a))))
  have hx := rootsOfUnityModuleExtEquiv_kummerModuleClass_mk X n hX (Additive.ofMul a)
  have hy := rootsOfUnityModuleExtEquiv_kummerModuleClass_mk Y n
    (isUnit_natCast_of_hom g hX) (Additive.ofMul (Units.map g.appTop.hom a))
  change extConstantAddEquivSheafH X _ 1 _ = _ at hx
  change extConstantAddEquivSheafH Y _ 1 _ = _ at hy
  let alpha := (etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).hom.app
    (rootsOfUnityModule.{u, 0} X n)
  let psi := (etaleModuleUnderlyingAbelian Y (ZMod n)).map
    (rootsOfUnityModuleInverseImageIso g n hX).hom
  have hcoeff : alpha ≫ psi = rootsOfUnityInverseImageComparison.{u, 0} g n := by
    change (etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).hom.app
      (rootsOfUnityModule.{u, 0} X n) ≫
        (etaleModuleForgetAb (ZMod n) Y).map
          (rootsOfUnityModuleInverseImageIso g n hX).hom = _
    erw [kummerTrace_forget_rootsModule_comparison, Iso.hom_inv_id_app_assoc]
  have hr := kummerOriginalComparison_restriction (ZMod n) g
    (rootsOfUnityModule.{u, 0} X n)
    (kummerModuleClassModuloPowers X n hX
      (QuotientAddGroup.mk (Additive.ofMul a)))
  have h1 := congrArg (fun z => Sheaf.H.map psi 1 z) hr
  have h2 := congrArg (fun z => Sheaf.H.map psi 1
    ((etaleCohomologyRestrictionMap.{u, 0, u + 1} g
      (rootsOfUnitySheaf.{u, 0} X n) 1 z).comp (Ext.mk₀ alpha) (add_zero 1))) hx
  let z := etaleCohomologyRestrictionMap.{u, 0, u + 1} g
    (rootsOfUnitySheaf.{u, 0} X n) 1
    (unitKummerClass X (NeZero.ne n) hX (Additive.ofMul a))
  have h3 := cohomologyMap_postcomp alpha psi 1 z
  have h4 := congrArg (fun f => Sheaf.H.map f 1 z) hcoeff
  have h5 := kummerModuleRestriction_ordinary g (NeZero.ne n) hX a
  exact hc.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans hy.symm)))))

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [NeZero n] in
/-- The inverse source square is the convention used by ExtCup.mapUnit. -/
theorem kummerModuleRestriction_unitSource :
    Functor.LaxMonoidal.ε (etaleModuleInverseImage (ZMod n) g) ≫
      (etaleModuleInverseImage (ZMod n) g).map
        (etaleModuleUnitIsoConstant (X := X) n).hom =
    (etaleModuleUnitIsoConstant (X := Y) n).hom ≫
      (etaleModuleInverseImageConstantIso (ZMod n) g).inv.app
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) := by
  have h := congrArg
    (fun z => Functor.LaxMonoidal.ε (etaleModuleInverseImage (ZMod n) g) ≫ z ≫
      (etaleModuleInverseImageConstantIso (ZMod n) g).inv.app
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))
    (kummerCorestrictionSource_unitIso_square g n)
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Functor.Monoidal.ε_η_assoc] at h
  -- The constant-sheaf functor composite and constantModuleSheaf are aliases.
  -- Specify the identity object before simplifying, avoiding reducibility-sensitive simp.
  change Functor.LaxMonoidal.ε (etaleModuleInverseImage (ZMod n) g) ≫
      ((etaleModuleInverseImage (ZMod n) g).map
        (etaleModuleUnitIsoConstant (X := X) n).hom ≫
        𝟙 ((etaleModuleInverseImage (ZMod n) g).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf
            (ZMod n) X.smallEtaleTopology))) =
    (etaleModuleUnitIsoConstant (X := Y) n).hom ≫
      (etaleModuleInverseImageConstantIso (ZMod n) g).inv.app
        (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))) at h
  rw [Category.comp_id] at h
  exact h

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [NeZero n] in
/-- Native mapUnit on a constant-source class, through the original unit isomorphism. -/
theorem kummerModuleRestriction_mapUnit {M : EtaleModules.{u, 0} (ZMod n) X} {q : ℕ}
    (a : Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology) M q) :
    Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod n) g)
      ((Ext.mk₀ (etaleModuleUnitIsoConstant (X := X) n).hom).comp a (zero_add q)) =
    (Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom).comp
      (etaleModuleExtRestriction (ZMod n) g M q a) (zero_add q) := by
  simp only [Stacks.ExtCup.mapUnit, etaleModuleExtRestriction, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  rw [kummerModuleRestriction_unitSource]

/-- Restriction of the original unit-source Kummer class on unit representatives. -/
theorem kummerModuleRestriction_unitClass (a : (Γ(X, ⊤))ˣ) :
    (Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod n) g)
      (kummerModuleUnitClass n hX (QuotientAddGroup.mk (Additive.ofMul a)))).comp
      (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).hom) (add_zero 1) =
    kummerModuleUnitClass n (isUnit_natCast_of_hom g hX)
      (QuotientAddGroup.mk (Additive.ofMul (Units.map g.appTop.hom a))) := by
  change (Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod n) g)
      ((Ext.mk₀ (etaleModuleUnitIsoConstant (X := X) n).hom).comp
        (kummerModuleClassModuloPowers X n hX
          (QuotientAddGroup.mk (Additive.ofMul a))) (zero_add 1))).comp _ _ =
    (Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom).comp
      (kummerModuleClassModuloPowers Y n (isUnit_natCast_of_hom g hX)
        (QuotientAddGroup.mk (Additive.ofMul (Units.map g.appTop.hom a)))) (zero_add 1)
  have hm := kummerModuleRestriction_mapUnit g n
    (kummerModuleClassModuloPowers X n hX
      (QuotientAddGroup.mk (Additive.ofMul a)))
  have hp := congrArg (fun z => z.comp
    (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).hom) (add_zero 1)) hm
  have hc := congrArg
    (fun z => (Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom).comp z
      (zero_add 1)) (kummerModuleRestriction_class g n hX a)
  exact hp.trans ((Ext.comp_assoc_of_third_deg_zero
    (Ext.mk₀ (etaleModuleUnitIsoConstant (X := Y) n).hom)
    (etaleModuleExtRestriction (ZMod n) g (rootsOfUnityModule.{u, 0} X n) 1
      (kummerModuleClassModuloPowers X n hX
        (QuotientAddGroup.mk (Additive.ofMul a))))
    (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).hom) (zero_add 1)).trans hc)

end Stacks.Kummer
end
