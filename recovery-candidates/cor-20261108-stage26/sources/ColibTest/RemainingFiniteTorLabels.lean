/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorLabels

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

-- The consumer has no supplied coefficient family, degree cutoff, or image-label injectivity.
example {r : ℕ}
    (s : Fin r → A)
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
          (Stacks.Length.primeResidueDegree (algebraMap R B)
            (p.asIdeal.comap (algebraMap R B)) p.asIdeal : ℤ) *
          Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal.comap (algebraMap R B)) :=
  finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_originalLabels
    k f g h i z w v hz hw x s hs

#check Stacks.Chow.finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_genericPoints
#check Stacks.Chow.finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_originalLabels
