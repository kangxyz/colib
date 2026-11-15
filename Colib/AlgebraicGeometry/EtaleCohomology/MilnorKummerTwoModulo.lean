/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.MilnorKummerTwo
/-! # Reduction of the native degree-two Kummer symbol modulo n

This uses the literal subgroup of multiples in native Milnor K₂, without changing
its symbols or the original cup-product target.
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

omit [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The field-unit quotient is annihilated by the coefficient level. -/
theorem fieldUnitModuloPowers_nsmul (a : Additive kˣ) :
    n • fieldUnitModuloPowers k n a = 0 := by
  change n • (QuotientAddGroup.mk' (Stacks.Kummer.unitMultiples (Spec (.of k)) n))
    ((Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom).toAdditive a) = 0
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨_, rfl⟩

/-- A multiple in the first unit input has zero original Kummer cup. -/
theorem fieldUnitKummerCup_nsmul_left (a b : Additive kˣ) :
    fieldUnitKummerCup k n (n • a) b = 0 := by
  change Stacks.Kummer.kummerCupModuloPowers (𝟙 (Spec (.of k))) n _
    (fieldUnitModuloPowers k n (n • a)) (fieldUnitModuloPowers k n b) = 0
  rw [map_nsmul, fieldUnitModuloPowers_nsmul, map_zero, AddMonoidHom.zero_apply]

/-- The tensor-square symbol is annihilated by the coefficient level. -/
theorem nsmul_kummerTensorSquare (t : TensorProduct ℤ (Additive kˣ) (Additive kˣ)) :
    n • kummerTensorSquare k n t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      rw [kummerTensorSquare_tmul]
      have h := DFunLike.congr_fun (map_nsmul (fieldUnitKummerCup k n) n a) b
      rw [AddMonoidHom.nsmul_apply, fieldUnitKummerCup_nsmul_left] at h
      exact h.symm
  | add x y hx hy => simp only [map_add, smul_add, hx, hy, add_zero]

/-- The original degree-two Milnor symbol is annihilated by the coefficient level. -/
theorem nsmul_milnorTwoKummerSymbol (x : MilnorKTheory k 2) :
    n • milnorTwoKummerSymbol k n x = 0 := by
  obtain ⟨t, rfl⟩ := milnorKTwoToKGroup_surjective k x
  change n • (MilnorK.K2.pairSteinbergSpan k).liftQ (kummerTensorSquare k n)
    (pairSteinbergSpan_le_ker k n)
    (MilnorK.K2.pairPresentationEquiv k (milnorKTwoToKGroup k t)) = 0
  rw [MilnorK.K2.pairPresentationEquiv_toKGroup, Submodule.liftQ_apply]
  exact nsmul_kummerTensorSquare k n t

/-- The actual cup symbol on the native Milnor quotient by multiples. -/
@[colib_tag "COL-1242"]
def milnorTwoModuloKummerSymbol :
    (MilnorKTheory k 2 ⧸ (n • AddMonoidHom.id (MilnorKTheory k 2)).range) →+
      kummerTwoTarget k n :=
  QuotientAddGroup.lift _ (milnorTwoKummerSymbol k n).toAddMonoidHom (by
    rintro x ⟨y, rfl⟩
    change milnorTwoKummerSymbol k n (n • y) = 0
    rw [map_nsmul, nsmul_milnorTwoKummerSymbol])

/-- Reduction modulo n preserves the exact original ordered cup symbol. -/
theorem milnorTwoModuloKummerSymbol_pair (a b : Additive kˣ) :
    milnorTwoModuloKummerSymbol k n
      (QuotientAddGroup.mk (milnorKTwoToKGroup k (a ⊗ₜ[ℤ] b))) =
        fieldUnitKummerCup k n a b := by
  change milnorTwoKummerSymbol k n (milnorKTwoToKGroup k (a ⊗ₜ[ℤ] b)) = _
  exact milnorTwoKummerSymbol_pair k n a b

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
