module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentWeight

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

attribute [local instance] isIntegral_integralComponentAt

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "C" => fieldChowSituation K
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "q" => (correspondenceIncidenceMap f g h z w).toImage
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)
local notation3 (prettyPrint := false) "sT" => π' ≫ sJ

variable (x : correspondenceLeftImageIncidence f g h i z w v)
  (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D x₀


open Classical in
example
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (p : {p : PrimeSpectrum R // IsMin p}) (hp : I ≤ p.1.asIdeal) :
    ((Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRemainingImageComponentStalk f g h i z w v x t))).toNat : ℤ) =
      flatPullbackWeight C sT π'
        (relativeDimension (C).dimensionFunction (q ≫ sJ) t +
          (correspondenceThirdSupportDimension K h i v : ℤ)) ((T).fromSpecStalk x₀ p.1) :=
  length_correspondenceRemainingImageComponentStalk_eq_originalGradeWeight
    K f g h i z w v x t hz hw p hp

open Classical in
example
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    Koszul.seqEuler
      (fun j => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j))
      (correspondenceRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        if I ≤ p.1.asIdeal then
          flatPullbackWeight C sT π'
            (relativeDimension (C).dimensionFunction sJ (q t) +
              (correspondenceThirdSupportDimension K h i v : ℤ))
            ((T).fromSpecStalk x₀ p.1) *
              Koszul.seqEuler
                (fun j => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j))
                (R ⧸ p.1.asIdeal)
        else 0 :=
  seqEuler_correspondenceRemainingImageComponentStalk_nativeWeights K f g h i z w v x t hx s hs

#check correspondenceRemainingImageComponentGenericLabel_projection
#check length_correspondenceRemainingImageComponentStalk_eq_flatPullbackWeight
#check length_correspondenceRemainingImageComponentStalk_eq_originalGradeWeight
#check seqEuler_correspondenceRemainingImageComponentStalk_nativeWeights
