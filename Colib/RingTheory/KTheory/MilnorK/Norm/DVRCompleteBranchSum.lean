/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteRamifiedBranch
public import Colib.RingTheory.KTheory.MilnorK.Norm.WeightedBranches

/-!
# The full ramification-weighted coefficient branch sum

Scalar base change of the original polynomial norm and the proved local p-group
squares give the entire weighted residue sum. All uniformizer equations and
literal quotient maps are retained. No weighted fiber count is assumed here.

Adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/CompleteBranchSum.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 31–86.
The native chosen norm is the original simple norm on this quotient by the
accepted chosen comparison. No new polynomial Milnor model is introduced.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial MonicIrreducibleOfDegree AdjoinRoot IsLocalRing

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

/-- The finite native quotient structure supplied by the monic power basis. -/
local instance completeBranchFinite {k : Type u} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) : FiniteDimensional k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

/-- The restricted residue of the original norm is the full upper branch sum,
with each original vertical ramification exponent visible. -/
theorem ramification_restrict_dvrMilnorTameSymbol_milnorKNorm_eq_branch_sum
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)
    [Algebra S (AdjoinRoot (poly p))] [IsFractionRing S (AdjoinRoot (poly p))]
    [Fintype ({r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)})]
    (U : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)} → Type u)
    [∀ r, CommRing (U r)] [∀ r, IsDomain (U r)] [∀ r, IsDiscreteValuationRing (U r)]
    [∀ r, Algebra T (U r)] [∀ r, Module.Finite T (U r)]
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
    (j : ∀ r, S →+* U r) [∀ r, IsLocalHom (j r)]
    (hj : ∀ r s, AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2
      (algebraMap S (AdjoinRoot (poly p)) s) =
        algebraMap (U r) (AdjoinRoot (poly r.1.2)) (j r s))
    {π : R} {ϖ : S} {τ : T}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (hτ : Irreducible τ)
    (ρ : ∀ r, U r) (hρ : ∀ r, Irreducible (ρ r))
    (v : Tˣ) (a : ℕ) (ha : algebraMap R T π = (v : T) * τ ^ a)
    (w : ∀ r, (U r)ˣ) (b : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)} → ℕ)
    (hb : ∀ r, j r ϖ = (w r : U r) * ρ r ^ b r)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    a • milnorKTheoryMap (ResidueField.map (algebraMap R T)) n
      (dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x)) =
      ∑ r, b r • milnorKNorm (ResidueField T) (ResidueField (U r)) n
        (milnorKTheoryMap (ResidueField.map (j r)) n
          (dvrMilnorTameSymbol' S (AdjoinRoot (poly p)) n x)) := by
  classical
  have hc (r : R) : algebraMap F L (algebraMap R F r) =
      algebraMap T L (algebraMap R T r) := by
    rw [← IsScalarTower.algebraMap_apply R F L, ← IsScalarTower.algebraMap_apply R T L]
  have hr := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R T) (algebraMap F L) hc
      hπ hτ v a ha n) (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x)
  change dvrMilnorTameSymbol' T L n
      (milnorKTheoryMap (algebraMap F L) (n + 1)
        (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x)) =
    (a : ℤ) • milnorKTheoryMap (ResidueField.map (algebraMap R T)) n
      (dvrMilnorTameSymbol' R F n
        (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x)) at hr
  simp only [natCast_zsmul] at hr
  have hbase : milnorKTheoryMap (algebraMap F L) (n + 1)
      (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
          poly r.2 ∣ (poly p).map (algebraMap F L)},
        milnorKNorm L (AdjoinRoot (poly r.1.2)) (n + 1)
          (milnorKTheoryMap
            (AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2) (n + 1) x) := by
    have hidentity :
        (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[F] AdjoinRoot (poly p)).toRingEquiv.toRingHom =
          RingHom.id (AdjoinRoot (poly p)) := rfl
    simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap,
      hidentity, RingHom.comp_id] using
      milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv_of_fintype p
        (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[F] AdjoinRoot (poly p)) (n + 1) x
  rw [← hr, hbase, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  have : CharZero (AdjoinRoot (poly r.1.2)) :=
    charZero_of_injective_algebraMap (algebraMap L (AdjoinRoot (poly r.1.2))).injective
  exact dvrMilnorTameSymbol'_milnorKNorm_map_complete_of_pGroup
    S T (U r) (AdjoinRoot (poly p)) L (AdjoinRoot (poly r.1.2)) Ω ℓ hG (g r) (j r)
    (AdjoinRoot.map (algebraMap F L) (poly p) (poly r.1.2) r.2) (hj r)
    hϖ (hρ r) (w r) (b r) (hb r) n x

end Stacks.Chow

end
