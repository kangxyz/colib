module

import Colib.RingTheory.Koszul.RestrictionComparison

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {r : ℕ}

-- No flatness or regularity of either the map or the sequence is assumed.
example (f : Fin r → R) (M : ModuleCat.{u} S) :
    Koszul.seqComplexTensor f ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ≅
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).obj
        (Koszul.seqComplexTensor (fun j => algebraMap R S (f j)) M) :=
  Koszul.seqComplexTensorRestrictScalarsIso f M

example (f : Fin r → R) (M : ModuleCat.{u} S) (n : ℕ) :
    (Koszul.seqComplexTensor f
      ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).homology n ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((Koszul.seqComplexTensor (fun j => algebraMap R S (f j)) M).homology n) :=
  Koszul.homologySeqComplexTensorRestrictScalarsIso f M n
