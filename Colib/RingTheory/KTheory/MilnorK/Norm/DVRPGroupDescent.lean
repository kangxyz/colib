/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteBranchSum
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRWeightedBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRRestrictionKernel
public import Colib.RingTheory.AdjoinRoot.TensorScalarFactors

/-!
# Actual degree annihilation from all local p-group branches

The two independently proved full branch sums coincide. Their difference is
killed after ramification-weighted restriction; actual residue projection and
the finite DVR degree formula then give the fraction-field degree annihilator.

Adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/DVRPGroupDescent.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The original
residue-characteristic-zero assumptions, actual coefficient fields and
integral closures are retained. All norm maps are the existing native chosen norms.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open scoped TensorProduct

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The actual monic quotient is finite over its coefficient field. -/
local instance completeDescentRootFinite {k : Type*} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) : FiniteDimensional k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

universe u

/-- Equality of the actual two branch sums annihilates the original norm-residue
error by the coefficient field degree. No ramification scalar is cancelled. -/
theorem finrank_smul_norm_residue_difference_eq_zero_of_pGroup_branches
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L]
    [Algebra F L] [FiniteDimensional F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Module.Finite R T] [Module.IsTorsionFree R T]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L] [IsIntegralClosure T R L]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)
    [Algebra S (AdjoinRoot (poly p))] [IsFractionRing S (AdjoinRoot (poly p))]
    [Algebra R S] [IsScalarTower R S (AdjoinRoot (poly p))]
    [Module.Finite R S] [Module.IsTorsionFree R S] [IsIntegralClosure S R (AdjoinRoot (poly p))]
    [IsLocalHom (algebraMap R S)]
    (U : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)} → Type u)
    [∀ r, CommRing (U r)] [∀ r, IsDomain (U r)] [∀ r, IsDiscreteValuationRing (U r)]
    [∀ r, Algebra T (U r)] [∀ r, Module.Finite T (U r)]
    [∀ r, Module.IsTorsionFree T (U r)]
    [∀ r, Algebra S (U r)] [∀ r, Algebra R (U r)]
    [∀ r, IsScalarTower R S (U r)] [∀ r, IsScalarTower R T (U r)]
    [∀ r, IsLocalHom (algebraMap S (U r))] [∀ r, IsLocalHom (algebraMap R (U r))]
    [∀ r, IsLocalHom (algebraMap T (U r))]
    [∀ r, Algebra (U r) (AdjoinRoot (poly r.1.2))]
    [∀ r, IsScalarTower T (U r) (AdjoinRoot (poly r.1.2))]
    [∀ r, IsFractionRing (U r) (AdjoinRoot (poly r.1.2))]
    [∀ r, IsIntegralClosure (U r) T (AdjoinRoot (poly r.1.2))]
    (Ω : Type u) [Field Ω] [Algebra L Ω] [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (g : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)},
      AdjoinRoot (poly r.1.2) →ₐ[L] Ω)
    (hj : ∀ r s, AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2
      (algebraMap S (AdjoinRoot (poly p)) s) =
        algebraMap (U r) (AdjoinRoot (poly r.1.2)) (algebraMap S (U r) s))
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (ρ : ∀ r, U r) (hρ : ∀ r, Irreducible (ρ r))
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (w z : ∀ r, (U r)ˣ) (b c : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)} → ℕ)
    (hb : ∀ r, algebraMap S (U r) ϖ = (w r : U r) * ρ r ^ b r)
    (hc : ∀ r, algebraMap T (U r) τ = (z r : U r) * ρ r ^ c r)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    Module.finrank F L •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) -
        milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S (AdjoinRoot (poly p)) n x)) = 0 := by
  classical
  let : Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)} :=
    coefficientFactorFintype (algebraMap F L) (poly p) (ne_zero p)
  let B := Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
  obtain ⟨θ, hθ⟩ := IsLocalRing.residue_surjective B.gen
  have hcoordinates (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)}) :
      algebraMap (U r) (AdjoinRoot (poly r.1.2)) (algebraMap S (U r) θ) =
        tensorScalarFactorsEquiv p (irreducible p).separable
          (1 ⊗ₜ[F] (algebraMap S (AdjoinRoot (poly p)) θ)) r := by
    rw [tensorScalarFactorsEquiv_tmul_one]
    exact (hj r θ).symm
  have hsum := ramification_restrict_dvrMilnorTameSymbol_milnorKNorm_eq_branch_sum
    R S T p U Ω ℓ hG g (fun r => algebraMap S (U r)) hj
    hπ hϖ hτ ρ hρ v a ha w b hb n x
  have hweighted := milnorKNorm_residue_weighted_baseChange R F S (AdjoinRoot (poly p)) T L
    (fun r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)} => AdjoinRoot (poly r.1.2)) U
    (tensorScalarFactorsEquiv p (irreducible p).separable) θ hcoordinates
    hπ hϖ hτ u e he v a ha B hθ.symm ρ hρ w z b c hb hc n
    (dvrMilnorTameSymbol' S (AdjoinRoot (poly p)) n x)
  have hres : algebraMap (ResidueField R) (ResidueField T) =
      ResidueField.map (algebraMap R T) := by
    ext t
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t
    rfl
  apply finrank_smul_eq_zero_of_ramified_residue_restrict R T F L hπ hτ v a ha n
  rw [map_sub, smul_sub]
  apply sub_eq_zero.mpr
  simp only [milnorKTheoryMap_eq_transport, ← hres] at hsum
  simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
    hsum.trans hweighted.symm

end Stacks.Chow

end
