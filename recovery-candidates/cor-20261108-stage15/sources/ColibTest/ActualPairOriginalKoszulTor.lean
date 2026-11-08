/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow RingTheory.Sequence

universe u

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w)

example : Function.Surjective (correspondenceIncidenceSupportStalkMap f g h z w x) :=
  correspondenceIncidenceSupportStalkMap_surjective f g h z w x

example : (((correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom).comp
      (correspondenceIncidenceSupportStalkMap f g h z w x) =
    ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom :=
  correspondenceIncidenceSupportStalkMap_comp f g h z w x

example [Flat f] [Flat h] [IsSeparated g] {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)))
    (ht : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)))
        (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)) =
        Ideal.span (Set.range t)) (n : ℕ) :
    let D := (correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x)
    let φ := correspondenceIncidenceSupportStalkMap f g h z w x
    let β := ((correspondenceMiddlePair f g h).stalkMap
      (correspondenceIncidenceAmbientInclusion f g h z w x)).hom
    letI := correspondenceIncidenceTorSupportModule f g h z w x n
    Nonempty (correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[D]
      ((Koszul.seqComplexTensor (fun j => φ (β (t j))) D).homology n)) :=
  ⟨correspondenceIncidenceTorOriginalSupportLinearEquiv f g h z w x t ht hkt n⟩
