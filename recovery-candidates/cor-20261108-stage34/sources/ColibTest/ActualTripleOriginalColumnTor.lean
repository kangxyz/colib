module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalColumnTor

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

variable [Flat f] [Flat g] [Flat h] [Flat i] [IsSeparated h]

example
    (t : List ((pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i p)))
    (s : List ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i p)))
    (ht : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i p)) t)
    (hs : IsRegular ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i p)) s)
    (hY : IY = Ideal.ofList
      (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom))
    (hZ : IZ = Ideal.ofList
      (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom)) (a b : ℕ) :
    let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    let hr := correspondenceOriginalMiddleLists_regular_append f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x) t s ht hs hY hZ
    correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (s'.get j))
          (correspondenceRemainingFirstKoszulModule
            f g h i z w v x t' hr.1 hY b)).homology a) :=
  correspondenceOriginalMiddleListsLeftTorIsoRemainingKoszul
    f g h i z w v x t s ht hs hY hZ a b

example [Smooth g] [Smooth h] :
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)))
      (ht : IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t)
      (hs : IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s)
      (hY : IY = Ideal.ofList
        (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom))
      (hZ : IZ = Ideal.ofList
        (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom)),
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      let hr := correspondenceOriginalMiddleLists_regular_append f g h i
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x) t s ht hs hY hZ
      ∀ a b : ℕ, Nonempty
        (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b ≅
          (ModuleCat.restrictScalars φ).obj
            ((Koszul.seqComplexTensor (fun j => φ (s'.get j))
              (correspondenceRemainingFirstKoszulModule
                f g h i z w v x t' hr.1 hY b)).homology a)) := by
  obtain ⟨t, s, ht, hs, hY, hZ⟩ := exists_correspondenceOriginalMiddleLists f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)
  exact ⟨t, s, ht, hs, hY, hZ, fun a b =>
    ⟨correspondenceOriginalMiddleListsLeftTorIsoRemainingKoszul
      f g h i z w v x t s ht hs hY hZ a b⟩⟩

end Stacks.Chow
