/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusTorsionFree
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSimplicialTensor
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Flatness of the actual integral reduced torus terms -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicTopology AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The simultaneous splitting makes reduced sections torsion-free. -/
instance reducedTorusSections_hasUniqueDiv (q : ℕ) (X : Cor k) :
    HasUniqueDiv (sections (reducedTorus k q) X) where
  nsmul_right_injective n hn := reducedTorus_sections_nsmul_injective k q X n hn

/-- The actual reduced correspondence sections are flat over the integers. -/
instance reducedTorusSections_flat (q : ℕ) (X : Cor k) :
    Module.Flat ℤ (sections (reducedTorus k q) X) := inferInstance

/-- Flatness holds on every actual ordinary smooth-site section. -/
instance reducedTorusIntPresheaf_sections_flat (q : ℕ)
    (X : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ) :
    Module.Flat ℤ ((reducedTorusIntPresheaf k q).obj X) :=
  reducedTorusSections_flat k q ((Cor.graphFunctor k).obj X.unop)

/-- Every simplex term is the same reduced presheaf evaluated on a product with a simplex. -/
instance reducedTorusIntSimplicial_sections_flat (q : ℕ) (n : SimplexCategoryᵒᵖ)
    (X : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ) :
    Module.Flat ℤ (((reducedTorusIntSimplicial k q).obj n).obj X) :=
  reducedTorusIntPresheaf_sections_flat k q
    (op (SmoothSite.product X.unop ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n.unop)))

end AlgebraicGeometry.PresheafWithTransfers
