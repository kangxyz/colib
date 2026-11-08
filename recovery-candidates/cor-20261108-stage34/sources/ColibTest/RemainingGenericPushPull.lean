module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingGenericPushPull

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "C" => fieldChowSituation K
local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "q" => (correspondenceIncidenceMap f g h z w).toImage
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "π" => correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)
local notation3 (prettyPrint := false) "sI" => q ≫ sJ
local notation3 (prettyPrint := false) "sE" => π ≫ sI
local notation3 (prettyPrint := false) "sT" => π' ≫ sJ


open Classical in
example
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (p : {p : PrimeSpectrum (correspondenceRemainingImageStalk f g h i z w v x) // IsMin p}) :
    (T).fromSpecStalk (correspondenceLeftImageIncidenceInclusion f g h i z w v x) p.1 ∈
      genericPoints T :=
  correspondenceRemainingImageStalk_minimal_generic K f g h i z w v x p

open Classical in
example
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w) (p : genericPoints T) (hp : π' p.1 = q t) :
    letI := isFinite_correspondenceIncidenceToImage f g h z w hz hw
    letI := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
    ((q).residueDegree t : ℤ) * flatPullbackWeight C sT π'
      (relativeDimension (C).dimensionFunction sI t +
        (correspondenceThirdSupportDimension K h i v : ℤ)) p.1 =
      ∑ᶠ η : {η : genericPoints E // q' η.1 = p.1},
        if π η.1.1 = t then
          (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
            ((q').residueDegree η.1.1 : ℤ)
        else 0 :=
  correspondenceLeftImage_fixedLabel_genericPushPull K f g h i z w v hz hw t p hp

#check correspondenceLeftIntermediateImageMap_preimage_generic
#check correspondenceRemainingImageStalk_minimal_generic
#check correspondenceLeftImage_fixedLabel_genericPushPull
