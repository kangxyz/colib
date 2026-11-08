/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.TensorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalMiddleLists

/-!
# Actual triple Tor and the remaining-first coefficient total

The actual sixfold Tor model is identified with the total of the remaining original middle
Koszul complex tensored with the first middle Koszul complex with the original full exterior
coefficients. This is a chain isomorphism, not merely an equality of Euler characteristics.
The native signed flip switches the two diagonal resolutions; the native coproduct comparison
and ordinary associator move the unchanged coefficient module into the first-stage complex.

This supplies the exact total whose column homology is used in first-stage Euler devissage.
The original middle lists are chosen in their original self-product stalks and pulled by the
actual sixfold maps. Their regularity is constructed in `TripleOriginalMiddleLists`; no new
lists or caller-supplied comparison are introduced here. The scalar descent of that column
homology to the literal first-stage incidence stalk is in `TripleFirstStageAction`.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Associativity/TwoListTorComparison.lean, blob
8cf7b487bd35ba9bb0beafa98a3053ca8deef708. The native exterior-power complexes replace the
original recursive list model. Finite generic Euler identities and the Cor bracket-to-sum
comparison remain distinct obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The remaining-first total, with full exterior coefficients in the first-stage complex. -/
abbrev correspondenceTripleIncidenceRemainingTotal
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :=
  HomologicalComplex.tensorObj (Koszul.seqComplex s.get)
    (Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x))

/-- The signed chain comparison from the actual coefficient total to the remaining-first total. -/
def correspondenceTripleIncidenceTwoListIsoRemainingTotal
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :
    correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s ≅
      correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s :=
  ChainComplex.tensorCoefficientsReverseIso
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)
      (Koszul.seqComplex t.get) (Koszul.seqComplex s.get) ≪≫
    whiskerLeftIso (Koszul.seqComplex s.get) (Koszul.tensoringRightSeqComplexIso t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x))

/-- The two actual totals have equal ambient module lengths in every homology degree. -/
theorem correspondenceTripleIncidenceTwoList_length_eq_remainingTotal
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) (n : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      ((correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s).homology n) =
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s).homology n) :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (correspondenceTripleIncidenceTwoListIsoRemainingTotal
      f g h i z w v x t s)).toLinearEquiv.length_eq

/-- Actual sixfold Tor is the homology of the genuine remaining-first total in every degree. -/
def correspondenceTripleIncidenceTorIsoRemainingTotal [IsSeparated g] [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) (t ++ s))
    (hker : Ideal.ofList (t ++ s) =
      RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom) (n : ℕ) :
    correspondenceTripleIncidenceTor f g h i z w v x n ≅
      (correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s).homology n :=
  correspondenceTripleIncidenceTorIsoTwoListTotal f g h i z w v x t s hr hker n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (correspondenceTripleIncidenceTwoListIsoRemainingTotal f g h i z w v x t s)

/-- Constructed original middle lists give the remaining-first total, with no comparison input. -/
theorem exists_correspondenceOriginalMiddleLists_remainingTotal_iso
    [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t ∧
      RingTheory.Sequence.IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s ∧
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList t' ∧
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList s' ∧
      ∀ n : ℕ, Nonempty (correspondenceTripleIncidenceTor f g h i z w v x n ≅
        (correspondenceTripleIncidenceRemainingTotal f g h i z w v x t' s').homology n) := by
  dsimp only
  obtain ⟨t, s, ht, hs, hkt, hks, he⟩ :=
    exists_correspondenceOriginalMiddleLists_tor_iso f g h i z w v x
  refine ⟨t, s, ht, hs, hkt, hks, fun n => ?_⟩
  obtain ⟨e⟩ := he n
  exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (correspondenceTripleIncidenceTwoListIsoRemainingTotal f g h i z w v x _ _)⟩

end Stacks.Chow
