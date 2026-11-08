module

import Colib.RingTheory.Koszul.GenericEuler

open Koszul

#check seqEuler
#check cast_seqEuler_eq_hilbertSamuelMultiplicity
#check ringKrullDim_le_of_seq_idealOfDefinition
#check seqEuler_eq_finsum_dim_eq
#check seqEuler_eq_zero_of_supportDim_lt
#check seqEuler_eq_finsum_minimalPrimes
#check sum_signed_seqEuler_eq_finsum_minimalPrimes

example {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {r : ℕ} (f : Fin r → R)
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) :
    seqEuler f M = ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
      ((Module.length (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule p.1.asIdeal.primeCompl M)).toNat : ℤ) *
          seqEuler f (R ⧸ p.1.asIdeal) :=
  seqEuler_eq_finsum_minimalPrimes f M hI

-- Arbitrary finite coefficient families retain their signs before generic dévissage.
example {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {r : ℕ} (f : Fin r → R) (M : ℕ → Type*)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] [∀ j, Module.Finite R (M j)]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) (s : Finset ℕ) :
    ∑ j ∈ s, (-1 : ℤ) ^ j * seqEuler f (M j) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ j ∈ s, (-1 : ℤ) ^ j *
          ((Module.length (Localization.AtPrime p.1.asIdeal)
            (LocalizedModule p.1.asIdeal.primeCompl (M j))).toNat : ℤ)) *
              seqEuler f (R ⧸ p.1.asIdeal) :=
  sum_signed_seqEuler_eq_finsum_minimalPrimes f M hI s
