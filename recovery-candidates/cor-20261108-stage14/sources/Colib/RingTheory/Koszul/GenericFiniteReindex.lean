/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.GenericFiniteEuler
import all Colib.RingTheory.Koszul.GenericEuler

/-!
# All original generic labels in finite-pushforward Euler devissage

A minimal source prime of a finite algebra need not contract to a minimal target
prime. Such vertical components are retained: their target quotient has smaller
dimension, so native generic Euler devissage proves their contribution zero.
Only after this vanishing is proved is the finite-fibre sum reindexed over every
original minimal source label. Colliding image labels remain separate summands.

The signed-family formula keeps each original homology coefficient and the
genuine residue degree of that original prime. It does not replace a Tor cycle
by the fundamental cycle of the full incidence. The algebra may be nonreduced,
nonlocal, disconnected, nonflat over its target, and of mixed dimension.

The private dimension bridge of `GenericEuler` is reused through `import all`;
the native prime-filtration and finite-fibre arguments are not reproved here.
The geometric original-label and residue-field identifications remain separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace Koszul

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [IsNoetherianRing R] [IsLocalRing R] {r : ℕ}

/-- A prime which is not minimal contributes zero to the remaining Euler
characteristic. Finite colength gives the ambient dimension bound. -/
theorem seqEuler_quotient_eq_zero_of_not_isMin
    (f : Fin r → R) (hI : IsIdealOfDefinition (Ideal.span (Set.range f)))
    (p : PrimeSpectrum R) (hp : ¬ IsMin p) : seqEuler f (R ⧸ p.asIdeal) = 0 := by
  have hd : Module.supportDim R (R ⧸ p.asIdeal) < (r : WithBot ℕ∞) := by
    rw [Module.supportDim_quotient_eq_ringKrullDim]
    exact lt_of_le_of_ne
      ((coheight_eq_ringKrullDim_quotient p).symm.trans_le
        ((Order.coheight_le_krullDim p).trans
          (ringKrullDim_le_of_seq_idealOfDefinition f hI)))
      (fun he => hp (isMin_of_quotient_dim_eq f hI p he))
  exact seqEuler_eq_zero_of_supportDim_lt f (R ⧸ p.asIdeal) hI hd

/-- Remaining Euler of the actual finite direct image, reindexed over every
original minimal source prime. No contraction injectivity or dominance is assumed. -/
theorem seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes
    (f : Fin r → R) (M : ModuleCat.{u} S) [Module.Finite S M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) :
    seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      ∑ᶠ q : {q : PrimeSpectrum S // IsMin q},
        (Stacks.Length.primeResidueDegree (algebraMap R S)
          (q.1.asIdeal.comap (algebraMap R S)) q.1.asIdeal : ℤ) *
            ((Module.length (Localization.AtPrime q.1.asIdeal)
              (LocalizedModule q.1.asIdeal.primeCompl M)).toNat : ℤ) *
                seqEuler f (R ⧸ q.1.asIdeal.comap (algebraMap R S)) := by
  classical
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let c := PrimeSpectrum.comap (algebraMap R S)
  let d : PrimeSpectrum R → PrimeSpectrum S → ℤ := fun p q =>
    Stacks.Length.primeResidueDegree (algebraMap R S) p.asIdeal q.asIdeal
  let w : PrimeSpectrum S → ℤ := fun q =>
    (Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M)).toNat
  let e : PrimeSpectrum R → ℤ := fun p => seqEuler f (R ⧸ p.asIdeal)
  let a : PrimeSpectrum S → ℤ := fun q => d (c q) q * w q * e (c q)
  let B : PrimeSpectrum R → ℤ := fun p =>
    (∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.asIdeal},
      d p q * w q) * e p
  let hP := PrimeSpectrum.finite_setOfPred_isMin R
  let hQ := PrimeSpectrum.finite_setOfPred_isMin S
  let P := hP.toFinset
  let Q := hQ.toFinset
  rw [seqEuler_restrictScalars_eq_finsum_generic_fibres f M hI]
  change (∑ᶠ p : {p : PrimeSpectrum R // IsMin p}, B p.1) =
    ∑ᶠ q : {q : PrimeSpectrum S // IsMin q}, a q.1
  rw [finsum_subtype_eq_finsum_cond (f := B),
    finsum_mem_eq_finite_toFinset_sum B hP,
    finsum_subtype_eq_finsum_cond (f := a),
    finsum_mem_eq_finite_toFinset_sum a hQ]
  change (∑ p ∈ P, B p) = ∑ q ∈ Q, a q
  have hB (p : PrimeSpectrum R) (hp : IsMin p) :
      B p = ∑ q ∈ Q with c q = p, a q := by
    have hfibre :
        (∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.asIdeal},
          d p q * w q) = ∑ q ∈ Q with c q = p, d p q * w q := by
      apply finsum_cond_eq_sum_of_cond_iff
      intro q _
      constructor
      · intro hq
        have hc : c q = p := PrimeSpectrum.ext hq
        refine Finset.mem_filter.mpr ⟨?_, hc⟩
        exact hQ.mem_toFinset.mpr (isMin_of_isMin_comap_finiteAlgebra q (hc.symm ▸ hp))
      · intro hq
        exact congrArg PrimeSpectrum.asIdeal (Finset.mem_filter.mp hq).2
    dsimp only [B]
    rw [hfibre, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only [a]
    rw [(Finset.mem_filter.mp hq).2]
  calc
    _ = ∑ p ∈ P, ∑ q ∈ Q with c q = p, a q :=
      Finset.sum_congr rfl fun p hp => hB p (hP.mem_toFinset.mp hp)
    _ = ∑ q ∈ Q with c q ∈ P, a q :=
      Finset.sum_fiberwise_eq_sum_filter Q P c a
    _ = ∑ q ∈ Q, a q := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hq hn
      have hp : ¬ IsMin (c q) := fun hp =>
        hn (Finset.mem_filter.mpr ⟨hq, hP.mem_toFinset.mpr hp⟩)
      have hz := seqEuler_quotient_eq_zero_of_not_isMin f hI (c q) hp
      change d (c q) q * w q * seqEuler f (R ⧸ (c q).asIdeal) = 0
      rw [hz, mul_zero]

/-- Actual higher-homology coefficients are summed with their original signs
at each original generic label before the remaining Euler factor is applied. -/
theorem sum_signed_seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes
    (f : Fin r → R) (M : ℕ → ModuleCat.{u} S) [∀ b, Module.Finite S (M b)]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) (J : Finset ℕ) :
    ∑ b ∈ J, (-1 : ℤ) ^ b *
      seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b)) =
      ∑ᶠ q : {q : PrimeSpectrum S // IsMin q},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ((Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) *
              (Stacks.Length.primeResidueDegree (algebraMap R S)
                (q.1.asIdeal.comap (algebraMap R S)) q.1.asIdeal : ℤ) *
                  seqEuler f (R ⧸ q.1.asIdeal.comap (algebraMap R S)) := by
  classical
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let Q := {q : PrimeSpectrum S // IsMin q}
  let : Fintype Q := (PrimeSpectrum.finite_setOfPred_isMin S).fintype
  let w : ℕ → Q → ℤ := fun b q =>
    (Module.length (Localization.AtPrime q.1.asIdeal)
      (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat
  let d : Q → ℤ := fun q => Stacks.Length.primeResidueDegree (algebraMap R S)
    (q.1.asIdeal.comap (algebraMap R S)) q.1.asIdeal
  let e : Q → ℤ := fun q => seqEuler f (R ⧸ q.1.asIdeal.comap (algebraMap R S))
  have hb (b : ℕ) :
      seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b)) =
        ∑ q : Q, d q * w b q * e q :=
    (seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes f (M b) hI).trans
      (finsum_eq_sum_of_fintype (fun q : Q => d q * w b q * e q))
  have hr : (∑ᶠ q : Q, (∑ b ∈ J, (-1 : ℤ) ^ b * w b q) * d q * e q) =
      ∑ q : Q, (∑ b ∈ J, (-1 : ℤ) ^ b * w b q) * d q * e q :=
    finsum_eq_sum_of_fintype _
  change (∑ b ∈ J, (-1 : ℤ) ^ b *
    seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b))) =
      ∑ᶠ q : Q, (∑ b ∈ J, (-1 : ℤ) ^ b * w b q) * d q * e q
  rw [hr]
  simp_rw [hb, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

end Koszul
