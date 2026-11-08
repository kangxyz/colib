module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteImageLabels

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u


variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "L" =>
  correspondenceRemainingOriginalGenericLabels f g h i z w v x

example (η : L) :
    (T).fromSpecStalk x₀ (correspondenceRemainingOriginalImagePrime f g h i z w v x η) =
      q' η.1.1 :=
  correspondenceRemainingOriginalImagePrime_fromSpecStalk f g h i z w v x η

example (p : PrimeSpectrum R) :
    {η : L // correspondenceRemainingOriginalImagePrime f g h i z w v x η = p} ≃
      {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p} :=
  correspondenceRemainingOriginalImagePrimeFiberEquiv f g h i z w v x p

example [IsSeparated h] [IsLocallyNoetherian T]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    Finite L :=
  finite_correspondenceRemainingOriginalGenericLabels f g h i z w v x hz hw

#check correspondenceRemainingOriginalImagePrime
#check correspondenceRemainingOriginalImagePrime_fromSpecStalk
#check correspondenceRemainingOriginalImagePrimeFiberEquiv
#check finite_correspondenceRemainingOriginalGenericLabels
