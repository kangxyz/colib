/-
Copyright (c) 2026 kangxyz and Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Native monic prime factorization over a normal domain

Only the fraction field is used as a UFD. Monic factors descend through the
native integrally-closed factor-descent theorem, and monic divisibility descends
through the native polynomial division theorem. The list retains repetitions.
No Noetherian or factorial assumption on the coefficient ring is needed.

Adapted from kangxyz/motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Aglib/RingTheory/Polynomial/Normal/MonicFactorization.lean,
verified source blob 16134979db6fe223dd8aa00600d655c7525a20b6.
Source-only construction; no kernel acceptance is asserted.
-/

@[expose] public noncomputable section

namespace Polynomial.NormalMonicFactorization

variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/-- A monic nonunit has an actual monic prime divisor, even over a nonfactorial normal ring. -/
theorem exists_monic_prime_factor {p : R[X]} (hp : p.Monic) (hunit : ¬ IsUnit p) :
    ∃ q : R[X], q.Monic ∧ Prime q ∧ q ∣ p := by
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmap : ¬ IsUnit (p.map (algebraMap R K)) :=
    fun h => hunit (hp.isPrimitive.isUnit_iff_isUnit_map.mpr h)
  obtain ⟨g, hg, hgirr, hgp⟩ := exists_monic_irreducible_factor _ hmap
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp hgp
  simp only [hg.leadingCoeff, C_1, mul_one] at hq
  have hmonic : q.Monic := monic_of_injective hinj (hq ▸ hg)
  have hprime : Prime q := by
    have hqprime : Prime (q.map (algebraMap R K)) := hq ▸ hgirr.prime
    refine ⟨hmonic.ne_zero,
      fun h => hqprime.not_isUnit (h.map (mapRingHom _)), ?_⟩
    intro a b hab
    have hm := map_dvd (algebraMap R K) hab
    rw [Polynomial.map_mul] at hm
    exact (hqprime.dvd_or_dvd hm).imp
      ((map_dvd_map _ hinj hmonic).mp) ((map_dvd_map _ hinj hmonic).mp)
  exact ⟨q, hmonic, hprime, (map_dvd_map _ hinj hmonic).mp (hq ▸ hgp)⟩

/-- Full monic prime factorization, with genuine invertible constant coefficients. -/
theorem exists_list_monic_prime_factors_of_normal (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) :
    ∃ factors : List R[X], factors.prod = p ∧
      ∀ q ∈ factors, q.Monic ∧ Prime q ∧ IsUnit (q.coeff 0) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hunit : IsUnit p
    · exact ⟨[], by simpa using (hp.eq_one_of_isUnit hunit).symm, by simp⟩
    obtain ⟨q, hq, hprime, r, hr⟩ := exists_monic_prime_factor hp hunit
    have hrmonic : r.Monic := hq.of_mul_monic_left (hr ▸ hp)
    have hc : IsUnit (q.coeff 0 * r.coeff 0) := by
      simpa only [hr, mul_coeff_zero] using hu
    have hdegree : q.natDegree + r.natDegree = p.natDegree := by
      rw [hr, natDegree_mul hq.ne_zero hrmonic.ne_zero]
    have hpos : 0 < q.natDegree := by
      by_contra h
      have hz : q.natDegree = 0 := by omega
      apply hprime.not_isUnit
      rw [eq_one_of_monic_natDegree_zero hq hz]
      exact isUnit_one
    obtain ⟨tail, htail, htailFactors⟩ := ih r.natDegree (by omega) r hrmonic
      (isUnit_of_mul_isUnit_right hc) rfl
    refine ⟨q :: tail, by simp [htail, ← hr], ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hq, hprime, isUnit_of_mul_isUnit_left hc⟩
    · exact htailFactors s hs

end Polynomial.NormalMonicFactorization
