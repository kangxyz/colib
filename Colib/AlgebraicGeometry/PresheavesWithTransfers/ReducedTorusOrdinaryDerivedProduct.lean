/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusPresheafAWQuasiIso
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Localizing the actual ordinary tensor span

The source is the localization of the ordinary tensor
chain complex. It is not identified with a derived tensor product.
-/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
universe u v
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable [HasDerivedCategory.{v}
  ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)]

/-- Embed nonnegative chains in nonpositive cochains and take the actual localization. -/
def integralPresheafChainToDerived :
    ChainComplex ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) ℕ ⥤
      DerivedCategory ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) :=
  ComplexShape.embeddingDownNat.extendFunctor _ ⋙ DerivedCategory.Q

/-- Only the localized AW map is inverted. -/
instance reducedTorusDerivedAW_isIso (q : ℕ) :
    IsIso ((integralPresheafChainToDerived k).map (reducedTorusPresheafAW k q)) := by
  change IsIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (reducedTorusPresheafAW k q)
      ComplexShape.embeddingDownNat))
  infer_instance

/-- The actual localized roof, with the ordinary total-tensor source retained literally. -/
def reducedTorusOrdinaryTensorDerivedProduct (q : ℕ) :
    (integralPresheafChainToDerived k).obj
      (HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k 1))) ⟶
    (integralPresheafChainToDerived k).obj
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k (q + 1))) :=
  inv ((integralPresheafChainToDerived k).map (reducedTorusPresheafAW k q)) ≫
    (integralPresheafChainToDerived k).map (reducedTorusPresheafChainPairing k q)

/-- The roof recovers the original right leg after precomposition by localized AW. -/
theorem reducedTorusOrdinaryTensorDerivedProduct_fac (q : ℕ) :
    (integralPresheafChainToDerived k).map (reducedTorusPresheafAW k q) ≫
      reducedTorusOrdinaryTensorDerivedProduct k q =
    (integralPresheafChainToDerived k).map (reducedTorusPresheafChainPairing k q) := by
  simp [reducedTorusOrdinaryTensorDerivedProduct]

end AlgebraicGeometry.PresheafWithTransfers
