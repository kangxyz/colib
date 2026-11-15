/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterConstantCoordinate
/-! # The literal parameter coordinate in every simplex degree -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Simplicial TensorProduct
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- The native unit map sends a scalar to that scalar times the pulled-back section. -/
theorem parameterUnitCoordinate_app (Q : (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) (T U : Sm) (b : Q.obj (op T))
    (z : ULift.{u + 1} ℤ) :
    ((parameterUnitCoordinate k Q T b).app (op U)).hom z =
      z.down • (Q.map (SmoothSite.productSnd U T).op).hom b := by
  change ((TensorProduct.congr ULift.moduleEquiv
    (LinearEquiv.refl ℤ (Q.obj (op (SmoothSite.product U T))))).trans
      (TensorProduct.lid ℤ (Q.obj (op (SmoothSite.product U T)))))
        (z ⊗ₜ[ℤ] (Q.map (SmoothSite.productSnd U T).op).hom b) = _
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, ULift.moduleEquiv_apply,
    LinearEquiv.refl_apply, TensorProduct.lid_tmul]
  exact int_smul_eq_zsmul _ _ _

/-- In every simplex degree the constant coordinate is pulled back only from the
parameter, with the original last-factor swap retained. -/
theorem simplicialConstantParameterCoordinate_app (Q : (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) (T U : Sm)
    (b : Q.obj (op T)) (n : ℕ) (z : ULift.{u + 1} ℤ) :
    (((simplicialConstantParameterCoordinate k Q T b).app (op ⦋n⦌)).app (op U)).hom z =
      z.down • (Q.map (SmoothSite.productFst (SmoothSite.product U T)
        (smoothSiteObj k n) ≫ SmoothSite.productSnd U T).op).hom b := by
  change (Q.map (SmoothSite.productSwapLast U T (smoothSiteObj k n)).op).hom
    (((parameterUnitCoordinate k Q T b).app
      (op (SmoothSite.product U (smoothSiteObj k n)))).hom z) = _
  rw [parameterUnitCoordinate_app]
  rw [map_zsmul]
  congr 1
  change (Q.map (SmoothSite.productSnd (SmoothSite.product U (smoothSiteObj k n)) T).op ≫
    Q.map (SmoothSite.productSwapLast U T (smoothSiteObj k n)).op) b = _
  simp only [← Q.map_comp, ← op_comp, SmoothSite.productSwapLast_snd]

end AlgebraicSimplex
