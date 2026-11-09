/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleCombinedColumnEuler
public import Colib.RingTheory.Koszul.EulerVanishing

/-!
# The actual right signed column computes the same combined triple Tor

The existing original-list left/right column equality already applies native local triple-Tor
associativity to the actual two diagonal quotients and full exterior support. Composing its
reverse with the proved left-column-to-combined-Tor comparison gives the right column without
re-proving that local theorem or introducing a comparison hypothesis. The same original Y/Z
lists, actual sixfold ring and full right-stage action are retained.

Bounded Z-Koszul homology extends the finite first-degree sum to the full signed finsum.
No actual original G,H Tor tensor comparison is assumed here; the following leaf applies the
already constructed right-stage-linear comparison to that literal coefficient module.

References: Stacks 0B1L, in its regular-local-ring form, and 0AZT. Source context:
independent motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b. This is a local coefficient theorem, not a
right weighted-cycle, right bracket, global associativity, or category assertion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The finite right signed column for the unchanged original lists equals actual triple Tor. -/
theorem sum_originalMiddleLists_rightEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
    ∀ (t : List RY) (s : List RZ) (_ht : IsRegular RY t) (hs : IsRegular RZ s)
      (_hY : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
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
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) := by
  dsimp only
  intro t s ht hs hY hZ
  exact (correspondenceOriginalMiddleLists_columnEuler_eq
    K f g h i z w v x t s ht hs hY hZ).symm.trans
      (correspondenceOriginalMiddleLists_remainingEuler_eq_combinedTor
        K f g h i z w v x t s ht hs hY hZ)

/-- The full signed right first-degree finsum equals the same actual combined triple Tor.
The discarded tail is proved zero from the literal original Z-Koszul complex. -/
theorem finsum_originalMiddleLists_rightEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
    ∀ (t : List RY) (s : List RZ) (_ht : IsRegular RY t) (hs : IsRegular RZ s)
      (_hY : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
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
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) := by
  dsimp only
  intro t s ht hs hY hZ
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
  let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
  let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
  let s' := s.map β
  let hs' := (correspondenceCommonSecondList_rightFirst_regular
    f g h i z w v x.1 s hs hZ).1
  let H := fun n => correspondenceRightRemainingFirstKoszulModule
    f g h i z w v x.1 s' hs' hZ n
  let F : ℕ → ℤ := fun n => (-1 : ℤ) ^ n *
    Koszul.seqEuler (fun j => κ ((t.map α).get j)) (H n)
  have hsupport : Function.support F ⊆ (Finset.range (s'.length + 1) : Set ℕ) := by
    intro n hn
    change n ∈ Finset.range (s'.length + 1)
    apply Finset.mem_range.mpr
    by_contra hbound
    have hlt : s'.length < n := by omega
    let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
    have hkoszul : Koszul.IsKoszulRegular s'.get :=
      (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := A)).2.2
        (by simpa only [List.ofFn_get] using hs')
    have hzero := Koszul.isZero_tor_of_lt s'.get hkoszul M hlt
    have hH := IsZero.of_iso hzero
      (Koszul.torIsoHomologySeqComplexTensor s'.get hkoszul M n).symm
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hH
    let : Subsingleton (H n) := hsub
    exact hn (by simp only [F, Koszul.seqEuler_eq_zero_of_subsingleton, mul_zero])
  change (∑ᶠ n, F n) = _
  calc
    (∑ᶠ n, F n) = ∑ n ∈ Finset.range (s'.length + 1), F n :=
      finsum_eq_sum_of_support_subset (f := F) hsupport
    _ = ∑ n : Fin (s'.length + 1), F n :=
      (Fin.sum_univ_eq_sum_range F (s'.length + 1)).symm
    _ = _ := sum_originalMiddleLists_rightEuler_eq_combinedTor
      K f g h i z w v x t s ht hs hY hZ

end Stacks.Chow
