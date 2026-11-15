/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterConstantCoordinateFormula
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

/-- Pullback along the native parameter projection. -/
def parameterProjectionPullback (P : Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (T : Sm) :
    P ⟶ (parameterReindex k T).obj P :=
  Functor.whiskerRight (NatTrans.op (SmoothSite.Contraction.projection T)) P

/-- The original insertion is the native right unit followed by projection and
constant coordinate, with the pointwise reindex tensor unchanged. -/
theorem tensorParameterInsertion_factor
    (P Q : Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (T : Sm) (b : Q.obj (op T)) :
    tensorParameterInsertion k P Q T b =
      (ρ_ P).inv ≫ (parameterProjectionPullback k P T ⊗ₘ parameterUnitCoordinate k Q T b) := by
  ext U s
  change (P.map (SmoothSite.productFst U.unop T).op).hom s ⊗ₜ[ℤ]
      (Q.map (SmoothSite.productSnd U.unop T).op).hom b =
    TensorProduct.map (P.map (SmoothSite.productFst U.unop T).op).hom
      ((parameterUnitCoordinate k Q T b).app U).hom (s ⊗ₜ[ℤ] ULift.up 1)
  rw [TensorProduct.map_tmul, parameterUnitCoordinate_app]
  simp only [one_zsmul]

end AlgebraicSimplex
