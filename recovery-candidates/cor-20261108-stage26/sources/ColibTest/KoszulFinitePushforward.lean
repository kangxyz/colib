module

import Colib.RingTheory.Koszul.FinitePushforward

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {r : ℕ}

open Koszul

-- A nonflat, nonlocal, nonreduced finite algebra is allowed.
example [IsLocalRing R] [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] (f : Fin r → R) (M : ModuleCat.{u} S)
    (hfin : ∀ n : Fin (r + 1), Module.length S
      ((seqComplexTensor (fun j => algebraMap R S (f j)) M).homology (n : ℕ)) ≠ ⊤) :
    seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      ∑ q : MaximalSpectrum S,
        seqEuler
          (fun j => algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S (f j)))
          (Localization.AtPrime q.asIdeal ⊗[S] M) *
            (Module.finiteAlgebraResidueDegree R S q : ℤ) :=
  Koszul.seqEuler_restrictScalars_eq_sum f M hfin
