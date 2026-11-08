module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRightAmbientColumn

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

example
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b ≅
      (Koszul.seqComplexTensor t.get
        ((Koszul.seqComplexTensor s.get M).homology b)).homology a :=
  correspondenceTripleIncidenceRightIteratedTorIsoAmbientKoszul
    f g h i z w v x t s ht hs hY hZ a b

example
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ)
    (hab : t.length < a ∨ s.length < b) :
    IsZero (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b) :=
  isZero_correspondenceTripleIncidenceRightIteratedTor_of_listLength_lt
    f g h i z w v x t s ht hs hY hZ a b hab

example
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length A
        (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)) =
      ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler t.get ((Koszul.seqComplexTensor s.get M).homology b) :=
  finsum_signed_rightIteratedTor_eq_sum_ambientFirstEuler
    f g h i z w v x t s ht hs hY hZ

end Stacks.Chow
