module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstCoefficientEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "I₀" => correspondenceIncidence f g h z w
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "π" => correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

variable (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x


example
    [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
    (∑ t : genericPoints I₀,
      (correspondenceIncidenceTorCoefficient K f g h z w t *
        ((correspondenceIncidenceMap f g h z w).residueDegree t.1 : ℤ)) *
          Koszul.seqEuler (fun j => α (s j))
            (correspondenceRemainingImageComponentStalk f g h i z w v x t.1)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K f g h z w
            (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) :=
  sum_firstTorCoefficient_mul_seqEuler_correspondenceRemainingImageComponentStalk
    K f g h i z w v x hz hw hx s hs

#check sum_firstTorCoefficient_mul_seqEuler_correspondenceRemainingImageComponentStalk
