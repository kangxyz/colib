/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootExtraction

/-! # Vanishing on the full root algebra

No field factor, primitive root, or norm-Kummer compatibility is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry Polynomial
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits
namespace Stacks.Kummer
open Stacks.EtaleCohomology

section Algebra
variable {R : Type u} [CommRing R] (n : ℕ) [NeZero n] (a : Rˣ)

/-- The unit whose value is the literal coordinate in the entire root algebra. -/
def kummerRootUnit : (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R)))ˣ :=
  (isUnit_root_unit (NeZero.ne n) a).unit

@[simp]
theorem kummerRootUnit_val :
    (kummerRootUnit n a : AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R))) =
      AdjoinRoot.root ((Polynomial.X : R[X]) ^ n - C (a : R)) := IsUnit.unit_spec _

/-- The actual unit satisfies the power equation, with no quotient-field choice. -/
theorem kummerRootUnit_pow :
    kummerRootUnit n a ^ n =
      Units.map (algebraMap R
        (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R)))).toMonoidHom a := by
  apply Units.ext
  change (kummerRootUnit n a : AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R))) ^ n = _
  rw [kummerRootUnit_val]
  exact root_pow_eq_unit a

/-- The original affine map from the whole root algebra. -/
def kummerRootSpecMap :
    Spec (.of (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R)))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R)))))

/-- Finiteness uses the actual full polynomial quotient. -/
theorem kummerRootSpecMap_finite : IsFinite (kummerRootSpecMap n a) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (finite_adjoinRoot_unit (NeZero.ne n) a)

/-- Inverting the degree makes that same full root algebra étale. -/
theorem kummerRootSpecMap_etale (hn : IsUnit (n : R)) : Etale (kummerRootSpecMap n a) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr (etale_adjoinRoot_unit hn (NeZero.ne n) a)

end Algebra

/-- Pullback of actual affine global units, retaining both ΓSpec identifications. -/
theorem kummerRoot_gammaSpecUnits {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Rˣ) :
    Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom
        (Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom a) =
      Units.map (Scheme.ΓSpecIso (.of S)).inv.hom.toMonoidHom (Units.map f.toMonoidHom a) := by
  apply Units.ext
  change (((Scheme.ΓSpecIso (.of R)).inv ≫
    (Spec.map (CommRingCat.ofHom f)).appTop).hom (a : R)) =
      (((CommRingCat.ofHom f) ≫ (Scheme.ΓSpecIso (.of S)).inv).hom (a : R))
  exact congrArg (fun z => z.hom (a : R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

/-- The pulled-back affine global unit is an actual power of a global unit. -/
theorem kummerRoot_globalUnit_pow {R : Type u} [CommRing R]
    (n : ℕ) [NeZero n] (a : Rˣ) :
    (Units.map (Scheme.ΓSpecIso
      (.of (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R))))).inv.hom.toMonoidHom
      (kummerRootUnit n a)) ^ n =
    Units.map (kummerRootSpecMap n a).appTop.hom
      (Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom a) := by
  rw [← map_pow, kummerRootUnit_pow]
  exact (kummerRoot_gammaSpecUnits
    (algebraMap R (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R)))) a).symm

section Vanishing
variable {Z : Scheme.{u}} (n : ℕ) [NeZero n]
  [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
  (hZ : IsUnit (n : Γ(Z, ⊤)))

/-- Actual powers vanish in the original module Kummer class. -/
theorem kummerModuleClass_power_zero (a b : (Γ(Z, ⊤))ˣ) (hb : b ^ n = a) :
    kummerModuleClassModuloPowers Z n hZ
      (QuotientAddGroup.mk (Additive.ofMul a)) = 0 := by
  apply (rootsOfUnityModuleExtEquiv Z n 1).injective
  rw [map_zero, rootsOfUnityModuleExtEquiv_kummerModuleClass_mk]
  exact (unitKummerClass_ofMul_eq_zero_iff Z (NeZero.ne n) hZ a).mpr ⟨b, hb⟩

/-- Actual powers vanish after the original unit-source change, too. -/
theorem kummerModuleUnitClass_power_zero (a b : (Γ(Z, ⊤))ˣ) (hb : b ^ n = a) :
    kummerModuleUnitClass n hZ (QuotientAddGroup.mk (Additive.ofMul a)) = 0 := by
  change (Ext.mk₀ (etaleModuleUnitIsoConstant (X := Z) n).hom).comp
    (kummerModuleClassModuloPowers Z n hZ
      (QuotientAddGroup.mk (Additive.ofMul a))) (zero_add 1) = 0
  erw [kummerModuleClass_power_zero n hZ a b hb, Ext.comp_zero]

end Vanishing

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the original unit-source Kummer class vanishes on the entire
root algebra. This uses no norm compatibility and no field-factor selection. -/
theorem kummerModuleUnitClass_rootRestriction_zero
    {R : Type u} [CommRing R] (n : ℕ) [NeZero n] (a : Rˣ) (hn : IsUnit (n : R))
    [HasExt.{u + 1} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (Spec (.of (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R))))).smallEtaleTopology
      AddCommGrpCat.{u + 1})] :
    let hX : IsUnit (n : Γ(Spec (.of R), ⊤)) := by
      simpa only [map_natCast] using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
    Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod n) (kummerRootSpecMap n a))
      (kummerModuleUnitClass n hX (QuotientAddGroup.mk (Additive.ofMul
        (Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom a)))) = 0 := by
  intro hX
  let g := kummerRootSpecMap n a
  let hY := isUnit_natCast_of_hom g hX
  let aX := Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom a
  let tY := Units.map (Scheme.ΓSpecIso
    (.of (AdjoinRoot ((Polynomial.X : R[X]) ^ n - C (a : R))))).inv.hom.toMonoidHom
      (kummerRootUnit n a)
  have hp : tY ^ n = Units.map g.appTop.hom.toMonoidHom aX := kummerRoot_globalUnit_pow n a
  have hz := kummerModuleUnitClass_power_zero n hY _ tY hp
  have hres := kummerModuleRestriction_unitClass g n hX aX
  have hres0 := hres.trans hz
  have h := congrArg
    (fun z => z.comp (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).inv)
      (add_zero 1)) hres0
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.zero_comp] using h

end Stacks.Kummer
end
