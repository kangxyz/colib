module

import Colib.RingTheory.Koszul.MappedRegularLength

open CategoryTheory

universe u

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] {r : ℕ}

-- Neither target regularity nor flatness of the coefficient map is required.
example [IsNoetherianRing R] [IsLocalRing R]
    (f : Fin r → A) (hf : RingTheory.Sequence.IsRegular A (List.ofFn f))
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range (fun j => algebraMap A R (f j)))))
    (n : ℕ) :
    Module.length R
      ((Koszul.seqComplexTensor (fun j => algebraMap A R (f j)) M).homology n) ≠ ⊤ :=
  Koszul.length_seqComplexTensor_map_ne_top_of_isRegular f hf M hI n
