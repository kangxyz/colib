module

import Colib.RingTheory.Koszul.GenericFiniteEuler

open CategoryTheory Koszul

universe u

#check isMin_of_isMin_comap_finiteAlgebra
#check lengthToNat_localized_restrictScalars_eq_finsum_fibre
#check seqEuler_restrictScalars_eq_finsum_generic_fibres
#check sum_signed_seqEuler_restrictScalars_eq_finsum_generic_fibres

-- A finite algebra may be nonreduced, nonlocal, nonflat and disconnected.
-- No contraction injectivity or finite-support premise is supplied.
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [IsNoetherianRing R] [IsLocalRing R] {r : ℕ}
    (f : Fin r → R) (M : ℕ → ModuleCat.{u} S) [∀ b, Module.Finite S (M b)]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) (J : Finset ℕ) :
    ∑ b ∈ J, (-1 : ℤ) ^ b *
      seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.1.asIdeal},
            (Stacks.Length.primeResidueDegree (algebraMap R S) p.1.asIdeal q.asIdeal : ℤ) *
              ((Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl (M b))).toNat : ℤ)) *
                  seqEuler f (R ⧸ p.1.asIdeal) :=
  sum_signed_seqEuler_restrictScalars_eq_finsum_generic_fibres f M hI J
