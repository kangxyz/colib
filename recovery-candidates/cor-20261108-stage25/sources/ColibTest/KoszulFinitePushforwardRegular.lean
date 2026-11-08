module

import Colib.RingTheory.Koszul.FinitePushforwardRegular

open CategoryTheory Koszul
open scoped TensorProduct

universe u

variable {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
  [Algebra A R] [Algebra R S] [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R S]
  {r : ℕ}

-- No flatness, localness or reducedness of S, and no finite-length input.
example [Fintype (MaximalSpectrum S)]
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ModuleCat.{u} S) [Module.Finite S M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range (fun j => algebraMap A R (f j))))) :
    seqEuler (fun j => algebraMap A R (f j))
      ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      ∑ q : MaximalSpectrum S,
        seqEuler (fun j => algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap R S (algebraMap A R (f j)))) (Localization.AtPrime q.asIdeal ⊗[S] M) *
            (Module.finiteAlgebraResidueDegree R S q : ℤ) :=
  Koszul.seqEuler_restrictScalars_eq_sum_of_isRegular f hf M hI
