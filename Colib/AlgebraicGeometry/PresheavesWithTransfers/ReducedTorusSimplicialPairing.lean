/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSectionPairing
public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Integral tensor linearization and all-simplex compatibility

This prepares the actual degreewise simplicial tensor
pairing; it is NOT a shuffle chain map or a derived tensor comparison.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry.Scheme
open scoped Simplicial TensorProduct
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ)

/-- Canonical integer-linearization of the verified biadditive section pairing. -/
def reducedTorusSectionBilinear :
    sections (reducedTorus k q) (Cor.mk U) →ₗ[ℤ]
      sections (reducedTorus k 1) (Cor.mk U) →ₗ[ℤ]
        sections (reducedTorus k (q + 1)) (Cor.mk U) where
  toFun s := (reducedTorusSectionPairing k U q s).toIntLinearMap
  map_add' s t := by
    ext b
    exact reducedTorusBinarySectionProduct_add_left k U q s t b
  map_smul' n s := by
    ext b
    exact congrArg (fun h => h b) ((reducedTorusSectionPairing k U q).map_zsmul n s)

/-- The actual ordinary integer tensor map on sections. -/
def reducedTorusSectionTensorMap :
    TensorProduct ℤ (sections (reducedTorus k q) (Cor.mk U))
      (sections (reducedTorus k 1) (Cor.mk U)) →ₗ[ℤ]
        sections (reducedTorus k (q + 1)) (Cor.mk U) :=
  TensorProduct.lift (reducedTorusSectionBilinear k U q)

/-- Every simplex operator, including faces and degeneracies, respects the
actual pairing on the literal products U × Δ. -/
theorem reducedTorusPairing_simplex_naturality
    {n m : SimplexCategory} (θ : n ⟶ m)
    (s : sections (reducedTorus k q)
      (Cor.mk (SmoothSite.product U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj m))))
    (b : sections (reducedTorus k 1)
      (Cor.mk (SmoothSite.product U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj m)))) :
    let f := SmoothSite.productMap (𝟙 U) ((AlgebraicSimplex.cosimplicialSmoothSite k).map θ)
    transfer (reducedTorus k (q + 1)) ((Cor.graphFunctor k).map f)
        (reducedTorusSectionPairing k _ q s b) =
      reducedTorusSectionPairing k _ q
        (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s)
        (transfer (reducedTorus k 1) ((Cor.graphFunctor k).map f) b) :=
  reducedTorusSectionPairing_naturality k _ q _ s b

end AlgebraicGeometry.PresheafWithTransfers
