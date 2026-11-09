/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleColumnEulerComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageCommonMiddleList

/-!
# The original Y and Z lists give the same actual signed column coefficient

The two lists live in the original middle self-product stalks. The existing
original-middle supplier chooses them once; their ordered images generate the
literal common diagonal ideals. Existing left successive regularity and right
common-Z regularity give the two canonical first-stage module actions for these
same lists. The actual local column equality is then applied, with all signs,
higher degrees and unreduced first-stage stalks retained.

No arbitrary replacement list or right-equivalence witness is used. No global
finite-image localization, admissibility assertion or cycle equality is inferred.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

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

/-- The same original middle lists compute equal genuine left and right column coefficients. -/
theorem correspondenceOriginalMiddleLists_columnEuler_eq
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
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s' hs' hZ b) := by
  dsimp only
  exact sum_signed_correspondenceTripleIncidence_columnEuler_eq k f g h i z w v x _ _
    (correspondenceOriginalMiddleLists_regular_append f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ).1
    (correspondenceCommonSecondList_rightFirst_regular f g h i z w v x.1 s hs hZ).1 hY hZ

/-- Smoothness chooses original middle lists once, with exact ideals and both actual
column Euler coefficients equal. The lists are not searched for by the caller. -/
theorem exists_correspondenceOriginalMiddleLists_columnEuler_eq :
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
          (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s' hs' hZ b) := by
  obtain ⟨t, s, ht, hs, hY, hZ⟩ := exists_correspondenceOriginalMiddleLists f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1)
  exact ⟨t, s, ht, hs, hY, hZ,
    correspondenceOriginalMiddleLists_columnEuler_eq k f g h i z w v x t s ht hs hY hZ⟩

end Stacks.Chow
