/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterInsertionFactor
/-! # Native projection and unit-coordinate factorization of parameter insertion -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct Simplicial
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- The native projection pullback transported through the genuine parameter swap. -/
def simplicialParameterProjectionPullback (P : Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (T : Sm) :=
  (simplicialPresheafFunctor k).map (parameterProjectionPullback k P T) ≫
    (simplicialPresheafParameterIso k T P).hom

/-- The original simplicial insertion factors through the actual projection and
constant parameter coordinate, not a replacement product map. -/
theorem simplicialTensorParameterInsertion_factor
    (P Q : Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (T : Sm) (b : Q.obj (op T)) :
    simplicialTensorParameterInsertion k P Q T b =
      (ρ_ (simplicialPresheaf k P)).inv ≫
        (simplicialParameterProjectionPullback k P T ⊗ₘ
          simplicialConstantParameterCoordinate k Q T b) := by
  ext n U s
  obtain ⟨⟨n⟩⟩ := n
  change TensorProduct.map
      (P.map (SmoothSite.productSwapLast U.unop T _).op).hom
      (Q.map (SmoothSite.productSwapLast U.unop T _).op).hom
      ((P.map (SmoothSite.productFst _ T).op).hom s ⊗ₜ[ℤ]
        (Q.map (SmoothSite.productSnd _ T).op).hom b) =
    TensorProduct.map
      ((P.map (SmoothSite.productFst _ T).op ≫
        P.map (SmoothSite.productSwapLast U.unop T _).op)).hom
      (((simplicialConstantParameterCoordinate k Q T b).app (op ⦋n⦌)).app U).hom
      (s ⊗ₜ[ℤ] ULift.up 1)
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
  congr 1
  change (Q.map (SmoothSite.productSwapLast U.unop T _).op).hom
    ((Q.map (SmoothSite.productSnd _ T).op).hom b) = _
  rw [simplicialConstantParameterCoordinate_app]
  simp only [one_zsmul]
  change (Q.map _ ≫ Q.map _) b = _
  simp only [← Q.map_comp, ← op_comp, SmoothSite.productSwapLast_snd]
  rfl

end AlgebraicSimplex
