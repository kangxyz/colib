/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleCoefficientTotal

/-!
# The two original middle orders in the common triple total

Both totals use the same actual sixfold stalk and the same full exterior structure module.
The accepted signed coefficient flip and the ordinary coefficient associator identify
`K(s) ⊗ K(t, M)` with `K(t) ⊗ K(s, M)`. The sign is the native total-complex sign, not an
unsigned exchange of factors. In particular, this is a chain isomorphism over the actual
ambient local ring, before taking homology or length.

The original-list existence theorem retains the lists in their original Y- and Z-middle
stalks, their actual pullback maps, and both actual diagonal ideal equalities. The same
sixfold Tor computes both total orders. No reversed regular-sequence hypothesis, right Tor
comparison, or geometric-integrality hypothesis is supplied by a caller.

The integer coefficient is the full alternating finsum of the actual homology lengths.
Its equality follows from equality of the extended-natural lengths in every degree, without
an arbitrary cutoff or a finite-length assumption. Proving finite length at the intended
generic points, and converting the iterated Euler expressions into correspondence brackets,
remain separate obligations. This file does not assert that total homology is iterated
homology, nor does it assert full Cor associativity.

Native providers: `ChainComplex.tensorCoefficientsIso`,
`ChainComplex.tensorCoefficientsReverseIso`, and `Koszul.tensoringRightSeqComplexIso`.
The accepted coefficient owner documents the pinned signed-flip construction and provenance.
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

/-- The unchanged coefficient total is the Z-first, Y-remaining total by the associator. -/
def correspondenceTripleIncidenceTwoListIsoRightRemainingTotal
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :
    correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s ≅
      correspondenceTripleIncidenceRemainingTotal f g h i z w v x s t :=
  ChainComplex.tensorCoefficientsIso
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)
      (Koszul.seqComplex t.get) (Koszul.seqComplex s.get) ≪≫
    whiskerLeftIso (Koszul.seqComplex t.get) (Koszul.tensoringRightSeqComplexIso s.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x))

/-- The two middle orders are isomorphic over the identical ambient stalk, with total signs. -/
def correspondenceTripleIncidenceRemainingTotalOrderIso
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :
    correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s ≅
      correspondenceTripleIncidenceRemainingTotal f g h i z w v x s t :=
  (correspondenceTripleIncidenceTwoListIsoRemainingTotal f g h i z w v x t s).symm ≪≫
    correspondenceTripleIncidenceTwoListIsoRightRemainingTotal f g h i z w v x t s

/-- Every homology degree has the same extended-natural length in the two original orders. -/
theorem length_correspondenceTripleIncidenceRemainingTotal_order
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) (n : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s).homology n) =
      Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x s t).homology n) :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (correspondenceTripleIncidenceRemainingTotalOrderIso
      f g h i z w v x t s)).toLinearEquiv.length_eq

/-- The full signed homology-length coefficients agree, without a chosen truncation. -/
theorem finsum_correspondenceTripleIncidenceRemainingTotal_order
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s).homology n)).toNat :
        ℤ)) =
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x s t).homology n)).toNat :
        ℤ) := by
  apply congrArg (fun a : ℕ → ℤ => ∑ᶠ n, a n)
  funext n
  rw [length_correspondenceTripleIncidenceRemainingTotal_order f g h i z w v x t s n]

/-- The same constructed original middle lists compute actual sixfold Tor in both orders. -/
theorem exists_correspondenceOriginalMiddleLists_bothTotalOrders
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
      ∀ n : ℕ,
        Nonempty (correspondenceTripleIncidenceTor f g h i z w v x n ≅
          (correspondenceTripleIncidenceRemainingTotal f g h i z w v x t' s').homology n) ∧
        Nonempty (correspondenceTripleIncidenceTor f g h i z w v x n ≅
          (correspondenceTripleIncidenceRemainingTotal f g h i z w v x s' t').homology n) := by
  dsimp only
  obtain ⟨t, s, ht, hs, hkt, hks, he⟩ :=
    exists_correspondenceOriginalMiddleLists_remainingTotal_iso f g h i z w v x
  refine ⟨t, s, ht, hs, hkt, hks, fun n => ?_⟩
  obtain ⟨e⟩ := he n
  exact ⟨⟨e⟩, ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (correspondenceTripleIncidenceRemainingTotalOrderIso f g h i z w v x _ _)⟩⟩

end Stacks.Chow
