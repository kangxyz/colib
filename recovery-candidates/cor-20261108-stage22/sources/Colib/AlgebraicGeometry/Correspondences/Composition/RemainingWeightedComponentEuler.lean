/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingLabelEulerReindex

/-!
# The concrete whole finite Tor family and weighted remaining image components

For the canonical modules obtained from each actual original pair Tor sheaf on
the entire finite model, the all-degree signed remaining Euler equals the sum
over all original first-incidence generic labels of the original signed Tor
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
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "R" =>
  correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" =>
  correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingFiniteTorModule f g h i z w v x.1
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

include hz hw

/-- The canonical whole finite Tor family, grouped by actual minimal image-stalk primes.
Nonminimal image labels are eliminated by proved Euler vanishing, not by an assumption. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_imagePrimes
    [IsLocallyNoetherian T] {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K f g h z w
            (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  exact (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedLabels
    K f g h i z w v hz hw x s hs).trans
      (finsum_originalExteriorLabels_eq_finsum_imagePrimes K f g h i z w v hz hw x s hs)

/-- Genuine weighted remaining-component Euler for the canonical original Tor family.
The original coefficient and residue degree are exactly those of `WeightedPairing`; each
remaining quotient is the full nonreduced image-component exterior stalk. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedComponents
    [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV] {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        (correspondenceIncidenceTorCoefficient K f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.1 : ℤ)) *
            Koszul.seqEuler (fun j => α (s j))
              (correspondenceRemainingImageComponentStalk f g h i z w v x.1 t.1) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftImageExteriorProjection f g h i z w v ≫ sJ)
  exact (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_imagePrimes
    K f g h i z w v hz hw x s hs).trans
      (sum_firstTorCoefficient_mul_seqEuler_correspondenceRemainingImageComponentStalk
        K f g h i z w v x.1 hz hw x.2 s hs).symm

end Stacks.Chow
