module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalColumnEuler

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : genericPoints (correspondenceTripleIncidence f g h i z w v))

local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "RY" =>
  (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
local notation3 (prettyPrint := false) "RZ" =>
  (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
local notation3 (prettyPrint := false) "α" =>
  ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
local notation3 (prettyPrint := false) "β" =>
  ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
local notation3 (prettyPrint := false) "φ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

example
    (t : List RY) (s : List RZ) (ht : IsRegular RY t) (hs : IsRegular RZ s)
    (hY : IY = Ideal.ofList (t.map α)) (hZ : IZ = Ideal.ofList (s.map β)) :
    let t' := t.map α
    let s' := s.map β
    let ht' := (correspondenceOriginalMiddleLists_regular_append f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ).1
    let hs' := (correspondenceCommonSecondList_rightFirst_regular
      f g h i z w v x.1 s hs hZ).1
    (∑ b : Fin (t'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => φ (s'.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t' ht' hY b)) =
    ∑ b : Fin (s'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => κ (t'.get j))
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s' hs' hZ b) :=
  correspondenceOriginalMiddleLists_columnEuler_eq
    k f g h i z w v x t s ht hs hY hZ

example :
    ∃ (t : List RY) (s : List RZ) (ht : IsRegular RY t) (hs : IsRegular RZ s)
      (hY : IY = Ideal.ofList (t.map α)) (hZ : IZ = Ideal.ofList (s.map β)),
      let t' := t.map α
      let s' := s.map β
      let ht' := (correspondenceOriginalMiddleLists_regular_append f g h i
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ).1
      let hs' := (correspondenceCommonSecondList_rightFirst_regular
        f g h i z w v x.1 s hs hZ).1
      (∑ b : Fin (t'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => φ (s'.get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t' ht' hY b)) =
      ∑ b : Fin (s'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => κ (t'.get j))
          (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s' hs' hZ b) :=
  exists_correspondenceOriginalMiddleLists_columnEuler_eq
    k f g h i z w v x

end Stacks.Chow
