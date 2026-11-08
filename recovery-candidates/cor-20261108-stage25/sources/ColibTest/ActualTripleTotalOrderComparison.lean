/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleTotalOrderComparison

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :
    correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s ≅
      correspondenceTripleIncidenceRemainingTotal f g h i z w v x s t :=
  correspondenceTripleIncidenceRemainingTotalOrderIso f g h i z w v x t s

example
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s).homology n)).toNat :
        ℤ)) =
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x s t).homology n)).toNat :
        ℤ) :=
  finsum_correspondenceTripleIncidenceRemainingTotal_order f g h i z w v x t s

example
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
          (correspondenceTripleIncidenceRemainingTotal f g h i z w v x s' t').homology n) :=
  exists_correspondenceOriginalMiddleLists_bothTotalOrders f g h i z w v x

end Stacks.Chow
