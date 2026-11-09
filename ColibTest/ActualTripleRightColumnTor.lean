module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRightColumnTor

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated h]
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x)
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

example
    (s : List A) (hs : IsRegular A s) (hZ : IZ = Ideal.ofList s) (b : ℕ) :
    (Koszul.seqComplexTensor s.get M).homology b ≅
      (ModuleCat.restrictScalars κ).obj
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b) :=
  correspondenceTripleIncidenceRightFirstKoszulRestrictIso
    f g h i z w v x s hs hZ b

example
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b ≅
      (ModuleCat.restrictScalars κ).obj
        ((Koszul.seqComplexTensor (fun j => κ (t.get j))
          (correspondenceRightRemainingFirstKoszulModule
            f g h i z w v x s hs hZ b)).homology a) :=
  correspondenceTripleIncidenceRightIteratedTorIsoRemainingKoszul
    f g h i z w v x t s ht hs hY hZ a b

example
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length A
        (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)) =
      ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => κ (t.get j))
          (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b) :=
  finsum_signed_rightIteratedTor_eq_sum_remainingFirstEuler
    f g h i z w v x t s ht hs hY hZ

end Stacks.Chow
