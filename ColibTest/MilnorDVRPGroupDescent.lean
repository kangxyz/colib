/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPGroupDescent

/-! Full-statement consumers for the complete-DVR source migration. -/

noncomputable section

open Stacks.Chow Polynomial Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

/-- Native monic quotients are finite over their original coefficient fields. -/
local instance consumerRootFinite {k : Type*} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) : FiniteDimensional k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis' (monic p)).finite

example
    {F L : Type u} [Field F] [CharZero F] [Field L] [CharZero L]
    [Algebra F L]
    (R S T : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [IsAdicComplete (maximalIdeal T) T] [CharZero (ResidueField T)]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    [Module.Finite R T] [Module.IsTorsionFree R T]
    [Algebra T L] [IsFractionRing T L] [Algebra R L]
    [IsScalarTower R F L] [IsScalarTower R T L]
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
  exact finrank_smul_norm_residue_difference_eq_zero_of_pGroup_branches
    R S T p U Ω ℓ hG g hj hπ hϖ hτ ρ hρ u e he v a ha w z b c hb hc n x

end
