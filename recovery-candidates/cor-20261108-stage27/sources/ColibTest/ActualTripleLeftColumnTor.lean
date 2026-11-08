module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleLeftColumnTor

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated g]
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  correspondenceRemainingOriginalStalk f g h i z w v x
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "φ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

variable (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
  (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ)

example :
    (Koszul.seqComplexTensor t.get M).homology b ≅
      (ModuleCat.restrictScalars φ).obj
        (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b) :=
  correspondenceTripleIncidenceFirstKoszulRestrictIso f g h i z w v x t ht hY b

example :
    correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (s.get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b)).homology a) :=
  correspondenceTripleIncidenceLeftIteratedTorIsoRemainingKoszul
    f g h i z w v x t s ht hs hY hZ a b

example :
    Module.length A (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b) =
      Module.length P ((Koszul.seqComplexTensor (fun j => φ (s.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b)).homology a) :=
  length_correspondenceTripleIncidenceLeftIteratedTor_eq_remainingKoszul
    f g h i z w v x t s ht hs hY hZ a b

end Stacks.Chow
