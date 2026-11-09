/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingLabelEulerReindex

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (hv :
    IsFiniteCorrespondencePoint h i v)

include hw hv

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) = Ideal.span (Set.range
        s)) :
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x.1
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let L := correspondenceRightRemainingOriginalGenericLabels f g h i z w v x.1
    (∑ᶠ η : L,
      (correspondenceIncidenceTorCoefficient K g h i w v
        (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
        ((q').residueDegree η.1.1 : ℤ) *
          Koszul.seqEuler (fun j => α (s j))
            (R ⧸ (correspondenceRightRemainingOriginalImagePrime f g h i z w v x.1 η).asIdeal)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K g h i w v
            (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal)  := by
  exact finsum_rightOriginalExteriorLabels_eq_finsum_imagePrimes
    K f g h i z w v hw hv x s hs

end Stacks.Chow
