/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding
public import Colib.RingTheory.AdjoinRoot.NestedTowerFactor
public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchFactorNativeTransport
public import Colib.RingTheory.KTheory.MilnorK.Norm.SeparableScalarFactors
public import Mathlib.Data.Fintype.BigOperators

/-!
# Native norm towers for actual matched scalar-factor branches

Every matched lower/relative pair is the actual canonical tower in the matching
top quotient. Literal identity-coefficient transport identifies its relative
norm, and the p-group tower theorem evaluates each branch. Expanding the outer
and inner norms and reindexing the entire dependent factor subtype gives the
restricted tower identity. There are no branchwise norm-comparison premises.

The splitting overfield has an independent universe. Only the original and
coefficient fields share the universe required by native Milnor restriction.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The p-group tower applies to every matched literal pair after the proved
identity-coefficient comparison of its relative polynomial and quotient map. -/
theorem simpleMilnorNorm_nestedScalarFactor_pGroup_tower
    {k K : Type u} [Field k] [Field K] [CharZero K]
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (s : {s : Σ a : ℕ, MonicIrreducibleOfDegree K a //
      poly s.2 ∣ (poly h).map φ})
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s.1.2) →ₐ[K] Ω)
    (y : MilnorKRing (AdjoinRoot (poly ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h)
      f s).2).1.2))) :
    simpleMilnorNorm ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1).1.2
      (simpleMilnorNorm ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2).1.2 y)
      =
      simpleMilnorNorm s.1.2 (milnorKRingMap ((AdjoinRoot.nestedScalarFactorQuotientEquiv φ (poly p)
        (poly h) f s)).toRingHom y) := by
  exact simpleMilnorNorm_pGroup_tower_of_native_factor_comparison
    ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1).1.2
    s.1.2
    (AdjoinRoot.nestedScalarFactorLowerAlgHom φ (poly p) (poly h) f s)
    ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2).1.2
    (AdjoinRoot.nestedScalarFactorTowerRingEquiv φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactorQuotientEquiv φ (poly p) (poly h) f s).toRingEquiv
    (AdjoinRoot.nestedScalarFactor_towerFactor_poly_eq_map_id φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactor_towerFactor_dvd_map_id φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactorTowerRingEquiv_toRingHom φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactorTowerRingEquiv_comp_towerFactorRingEquiv
      φ (poly p) (poly h) f s)
    ℓ hG j y

end Stacks.Chow
end
