/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingLabelEulerReindex

/-!
# The concrete whole finite Tor family and weighted remaining image components

For the canonical modules obtained from each actual original pair Tor sheaf on
the entire finite model, the all-degree signed remaining Euler equals the sum
over all original last-pair-incidence generic labels of the original signed Tor
coefficient times its original residue degree times the remaining Euler of the
full image-component exterior quotient. No family of modules or comparison
equality is supplied by the caller.

The proof joins the canonical sheaf-section family, its actual stalk and scalar
comparisons, the finite-model label bijections, native nonminimal-prime Euler
vanishing, and the fixed-label finite push-pull identity. The latter retains the
image exterior multiplicity, which the full quotient absorbs. Arbitrary fields,
split and colliding labels, and nilpotents remain present.

This is an integer Euler identity. The remaining actual pair-Tor comparison and
the global native cycle assembly have separate owners. It is not an assertion
of a completed associativity theorem or a Chow-group identity.
-/

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
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (hv :
    IsFiniteCorrespondencePoint h i v)

include hz hw hv

/-- The canonical whole finite Tor family, grouped by actual minimal image-stalk primes.
Nonminimal image labels are eliminated by proved Euler vanishing, not by an assumption. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_imagePrimes
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)] {r : ℕ}
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
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x.1
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K g h i w v
            (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) := by
  dsimp only
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  exact (finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedLabels
    K f g h i z w v hz hw hv x s hs).trans
      (finsum_rightOriginalExteriorLabels_eq_finsum_imagePrimes K f g h i z w v hw hv x s hs)

/-- Genuine weighted remaining-component Euler for the canonical original Tor family.
The original coefficient and residue degree are exactly those of `WeightedPairing`; each
remaining quotient is the full nonreduced image-component exterior stalk. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedComponents
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g)]
      [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g))] {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) = Ideal.span (Set.range
        s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient K g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) *
            Koszul.seqEuler (fun j => α (s j))
              (correspondenceRightRemainingImageComponentStalk f g h i z w v x.1 t.1) := by
  dsimp only
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceRightImageExteriorProjection f g h i z w v ≫ sJ)
  exact (finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_imagePrimes
    K f g h i z w v hz hw hv x s hs).trans
      (sum_firstTorCoefficient_mul_seqEuler_correspondenceRightRemainingImageComponentStalk
        K f g h i z w v x.1 hw hv x.2 s hs).symm

end Stacks.Chow
