module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedComponentEuler

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard


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

example
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
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) :=
  finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_imagePrimes
    K f g h i z w v hz hw x s hs

example
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
              (correspondenceRemainingImageComponentStalk f g h i z w v x.1 t.1) :=
  finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedComponents
    K f g h i z w v hz hw x s hs

#check finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_imagePrimes
#check finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedComponents
