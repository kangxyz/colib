/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerRootRestrictionVanishing
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleNorm
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleRootsOfUnityCupProjection
public import Colib.RingTheory.AdjoinRoot.SteinbergUnitNorm
public import Colib.Util.References

/-! # Steinberg vanishing for the original Kummer cup pairing

The proof uses the full root algebra and its actual unit
1-t, the actual restriction and norm corestrictions, and the native projection
formula. It does not assume the root polynomial is irreducible or the algebra is a field.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.SplitAffinePullback Polynomial
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits
  Stacks.EtaleCohomology.finiteEtaleZModDirectImage_preservesFiniteColimits
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
namespace Stacks.Kummer
open Stacks.EtaleCohomology

set_option maxHeartbeats 800000 in
-- The full root-algebra specialization combines the native norm, restriction and
-- projection maps; elaborating their concrete coefficient instances needs this budget.
set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- The original degree-two Kummer cup pairing kills the Steinberg pair (a,1-a).
Both units are transported by the actual ΓSpec isomorphism. -/
@[colib_tag "COL-1241"]
theorem kummerCupModuloPowers_steinberg
    {k : Type u} [Field k] (n : ℕ) [NeZero n] [NeZero (n : k)]
    (a : kˣ) (ha : IsUnit (1 - (a : k)))
    [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})] :
    let hX : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
      simpa only [map_natCast] using
        (IsUnit.mk0 (n : k) (NeZero.ne (n : k))).map (Scheme.ΓSpecIso (.of k)).inv.hom
    kummerCupModuloPowers (𝟙 (Spec (.of k))) n hX
      (QuotientAddGroup.mk (Additive.ofMul
        (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom a)))
      (QuotientAddGroup.mk (Additive.ofMul
        (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom ha.unit))) = 0 := by
  intro hX
  let A := AdjoinRoot ((Polynomial.X : k[X]) ^ n - C (a : k))
  let X₀ := Spec (.of k)
  let Y₀ := Spec (.of A)
  let g : Y₀ ⟶ X₀ := sourceMap (k := k) (A := A)
  let hn : IsUnit (n : k) := IsUnit.mk0 (n : k) (NeZero.ne (n : k))
  let : Module.Finite k A := finite_adjoinRoot_unit (NeZero.ne n) a
  let : Etale g := kummerRootSpecMap_etale n a hn
  let : IsFinite g := kummerRootSpecMap_finite n a
  let := etaleModules_enoughInjectives.{u, 0} (ZMod n) X₀
  let := etaleModules_enoughInjectives.{u, 0} (ZMod n) Y₀
  let M := rootsOfUnityModule.{u, 0} X₀ n
  let I := etaleModuleInverseImage (ZMod n) g
  let hY := isUnit_natCast_of_hom g hX
  let x := kummerModuleUnitClass n hX (QuotientAddGroup.mk (Additive.ofMul
    (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom a)))
  let t : Aˣ := AdjoinRoot.oneSubRootUnit n (a : k) ha
  let b : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod n) Y₀)) (I.obj M) 1 :=
    (kummerModuleUnitClass n hY (QuotientAddGroup.mk (Additive.ofMul
      (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t)))).comp
      (Ext.mk₀ (rootsOfUnityModuleInverseImageIso g n hX).inv) (add_zero 1)
  have hzero : Stacks.ExtCup.mapUnit I x = 0 :=
    kummerModuleUnitClass_rootRestriction_zero n a hn
  have hnorm := kummerModuleNorm_unitClass (k := k) (A := A) n hX t
  have ht : Units.map (Algebra.norm k) t = ha.unit :=
    AdjoinRoot.norm_oneSubRootUnit n (Nat.pos_of_ne_zero (NeZero.ne n)) (a : k) ha
  rw [ht] at hnorm
  obtain ⟨hG₁, hG₂, hG₃⟩ := exact_tensorRight_rootsOfUnityModule (𝟙 X₀) n
  obtain ⟨hLG₁, hLG₂, hLG₃⟩ :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
      (Λ := ZMod n) g M (locallyFiniteFree_rootsOfUnityModule (𝟙 X₀) n)
  have hproj := finiteEtaleRootsOfUnityUnitCorestriction_cup (𝟙 X₀) g n M
    (rfl : 1 + 1 = 2) x b
  change finiteEtaleZModUnitCorestriction n g (M ⊗ M) 2
      (Stacks.ExtCup.cup (Functor.LaxMonoidal.μ I M M)
        (Stacks.ExtCup.mapUnit I x) b rfl) =
    Stacks.ExtCup.cup (𝟙 (M ⊗ M)) x
      (finiteEtaleZModUnitCorestriction n g M 1 b) rfl at hproj
  rw [hzero, Stacks.ExtCup.zero_cup, map_zero, hnorm] at hproj
  change Stacks.ExtCup.cup (𝟙 (M ⊗ M)) x
      (kummerModuleUnitClass n hX (QuotientAddGroup.mk (Additive.ofMul
        (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom ha.unit)))) rfl = 0
  exact hproj.symm

end Stacks.Kummer
end
