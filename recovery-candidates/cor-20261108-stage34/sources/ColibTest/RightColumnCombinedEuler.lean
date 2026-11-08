/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightColumnCombinedEuler

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators

universe u

open Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
    ∀ (t : List RY) (s : List RZ) (ht : IsRegular RY t) (hs : IsRegular RZ s)
      (hY : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map α))
      (hZ : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map β)),
      let s' := s.map β
      let hs' := (correspondenceCommonSecondList_rightFirst_regular
        f g h i z w v x.1 s hs hZ).1
      (∑ n : Fin (s'.length + 1), (-1 : ℤ) ^ (n : ℕ) *
        Koszul.seqEuler (fun j => κ ((t.map α).get j))
          (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s' hs' hZ n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) :=
  sum_originalMiddleLists_rightEuler_eq_combinedTor K f g h i z w v x

example
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
    ∀ (t : List RY) (s : List RZ) (ht : IsRegular RY t) (hs : IsRegular RZ s)
      (hY : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map α))
      (hZ : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map β)),
      let s' := s.map β
      let hs' := (correspondenceCommonSecondList_rightFirst_regular
        f g h i z w v x.1 s hs hZ).1
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        Koszul.seqEuler (fun j => κ ((t.map α).get j))
          (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s' hs' hZ n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) :=
  finsum_originalMiddleLists_rightEuler_eq_combinedTor K f g h i z w v x
