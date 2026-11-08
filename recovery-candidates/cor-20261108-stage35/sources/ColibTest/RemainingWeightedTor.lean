/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedTor

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "R" =>
  correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" =>
  correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingFiniteTorModule f g h i z w v x.1

include hz hw

-- Both homological sums use the actual native Tor family and retain every original label.
example {r : ℕ}
    (s : Fin r → A) (hr : RingTheory.Sequence.IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ η : correspondenceRemainingOriginalGenericLabels f g h i z w v x.1,
        let q := (correspondenceRemainingFiniteGenericEquivOriginal
          f g h i z w v x.1).symm η
        let p := (correspondenceRemainingFiniteGenericEquivMinPrime
          f g h i z w v hz hw x.1 q).1
        (correspondenceIncidenceTorCoefficient k f g h z w
          (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
          ((correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree η.1.1 : ℤ) *
          (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
            ((Module.length (correspondenceRemainingAmbientStalk f g h i z w v x.1)
              (correspondenceRemainingImagePrimeTor f g h i z w v x.1 p n)).toNat : ℤ)) :=
  finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedTor
    k f g h i z w v hz hw x s hr hs

#check Stacks.Chow.finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedTor
