/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.KTheory.MilnorK.DegreeTwo
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerSteinberg
/-! # The degree-two Milnor Kummer symbol

Descend the actual Kummer cup through the native ordered-pair presentation of Milnor K₂.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
open scoped TensorProduct
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer
variable (k : Type u) [Field k] (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The original cup-product target with its unmodified roots-of-unity coefficients. -/
abbrev kummerTwoTarget :=
  Ext.{u + 1} (𝟙_ (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))))
    (Stacks.Kummer.rootsOfUnityModule.{u, 0} (Spec (.of k)) n ⊗
      Stacks.Kummer.rootsOfUnityModule.{u, 0} (Spec (.of k)) n) 2

/-- Field units mapped to the actual global-unit quotient. -/
def fieldUnitModuloPowers : Additive kˣ →+
    Stacks.Kummer.unitsModuloPowers (Spec (.of k)) n :=
  (QuotientAddGroup.mk' _).comp
    (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom).toAdditive

set_option maxRecDepth 4096 in
/-- The actual biadditive cup of field units. -/
def fieldUnitKummerCup : Additive kˣ →+ Additive kˣ →+ kummerTwoTarget k n := by
  let hX : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using
      (IsUnit.mk0 (n : k) (NeZero.ne (n : k))).map (Scheme.ΓSpecIso (.of k)).inv.hom
  let cup := Stacks.Kummer.kummerCupModuloPowers (𝟙 (Spec (.of k))) n hX
  exact AddMonoidHom.mk' (fun a => (cup (fieldUnitModuloPowers k n a)).comp
    (fieldUnitModuloPowers k n)) (by
      intro a b
      apply AddMonoidHom.ext
      intro c
      simp only [map_add, AddMonoidHom.comp_apply, AddMonoidHom.add_apply])

/-- The original pairing extended to the integral tensor square. -/
def kummerTensorSquare : TensorProduct ℤ (Additive kˣ) (Additive kˣ) →ₗ[ℤ]
    kummerTwoTarget k n :=
  (TensorProduct.liftAddHom (fieldUnitKummerCup k n) (by
    intro r a b
    simp only [map_zsmul, AddMonoidHom.zsmul_apply])).toIntLinearMap

/-- Evaluation of the tensor lift is the unchanged cup pairing. -/
theorem kummerTensorSquare_tmul (a b : Additive kˣ) :
    kummerTensorSquare k n (a ⊗ₜ[ℤ] b) = fieldUnitKummerCup k n a b := rfl

/-- The pair-symbol Steinberg submodule lies in the kernel of the actual cup. -/
theorem pairSteinbergSpan_le_ker :
    MilnorK.K2.pairSteinbergSpan k ≤ LinearMap.ker (kummerTensorSquare k n) := by
  apply Submodule.span_le.mpr
  rintro t ⟨a, b, hab, rfl⟩
  change fieldUnitKummerCup k n (Additive.ofMul a) (Additive.ofMul b) = 0
  have hb : (b : k) = 1 - (a : k) := eq_sub_of_add_eq' hab
  have ha : IsUnit (1 - (a : k)) := hb ▸ b.isUnit
  have hu : ha.unit = b := Units.ext (ha.unit_spec.trans hb.symm)
  have h := Stacks.Kummer.kummerCupModuloPowers_steinberg n a ha
  rw [hu] at h
  exact h

/-- The Kummer cup descends to the native degree-two Milnor group. -/
def milnorTwoKummerSymbol : MilnorKTheory k 2 →ₗ[ℤ] kummerTwoTarget k n :=
  ((MilnorK.K2.pairSteinbergSpan k).liftQ (kummerTensorSquare k n)
    (pairSteinbergSpan_le_ker k n)).comp (MilnorK.K2.pairPresentationEquiv k).toLinearMap

/-- The descended map retains each original ordered cup symbol. -/
theorem milnorTwoKummerSymbol_pair (a b : Additive kˣ) :
    milnorTwoKummerSymbol k n (milnorKTwoToKGroup k (a ⊗ₜ[ℤ] b)) =
      fieldUnitKummerCup k n a b := by
  change (MilnorK.K2.pairSteinbergSpan k).liftQ (kummerTensorSquare k n)
    (pairSteinbergSpan_le_ker k n)
    (MilnorK.K2.pairPresentationEquiv k (milnorKTwoToKGroup k (a ⊗ₜ[ℤ] b))) = _
  rw [MilnorK.K2.pairPresentationEquiv_toKGroup, Submodule.liftQ_apply]
  rfl
end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
