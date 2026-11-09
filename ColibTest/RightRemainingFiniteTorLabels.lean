/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorLabels

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (hv :
    IsFiniteCorrespondencePoint h i v)

include hz

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → ((pullback g g).presheaf.stalk
  (correspondenceRightImageMiddlePair f g h i z w v
    (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ η : correspondenceRightRemainingOriginalGenericLabels f g h i z w v x.1,
        let q := (correspondenceRightRemainingFiniteGenericEquivOriginal
          f g h i z w v x.1).symm η
        let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
          f g h i z w v hw hv x.1 q).1
        (correspondenceIncidenceTorCoefficient k g h i w v
          (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
          (Stacks.Length.primeResidueDegree (algebraMap R B)
            (p.asIdeal.comap (algebraMap R B)) p.asIdeal : ℤ) *
          Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal.comap (algebraMap R B))  := by
  exact finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_originalLabels
    k f g h i z w v hz hw hv x s hs

end Stacks.Chow
