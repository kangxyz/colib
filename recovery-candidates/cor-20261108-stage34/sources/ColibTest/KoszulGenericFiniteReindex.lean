module

import Colib.RingTheory.Koszul.GenericFiniteReindex

open CategoryTheory Koszul

universe u

#check seqEuler_quotient_eq_zero_of_not_isMin
#check seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes
#check sum_signed_seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes

-- Vertical contractions are proved zero, not excluded by a hypothesis.
example {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {r : ℕ} (f : Fin r → R) (hI : IsIdealOfDefinition (Ideal.span (Set.range f)))
    (p : PrimeSpectrum R) (hp : ¬ IsMin p) : seqEuler f (R ⧸ p.asIdeal) = 0 :=
  seqEuler_quotient_eq_zero_of_not_isMin f hI p hp

-- No S/R flatness, reducedness, equidimensionality, injectivity or
-- contraction-of-minimal-primes hypothesis is present.
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [IsNoetherianRing R] [IsLocalRing R] {r : ℕ}
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
                  seqEuler f (R ⧸ q.1.asIdeal.comap (algebraMap R S)) :=
  sum_signed_seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes f M hI J
