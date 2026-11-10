module

import Colib.AlgebraicGeometry.Correspondences.Exterior.QuotientIncidence

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open AlgebraicGeometry.Scheme

noncomputable section
universe u
variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

example : IsPullback (nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
    (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw)
    (correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w)
    (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw) :=
  nativeExteriorIncidenceQuotient_isPullback X Y Z T z w hz hw

example : IsClosedImmersion (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw) :=
  inferInstance

example (x : nativeExteriorIncidence X Y Z T z w hz hw) :
    correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w
      (nativeExteriorIncidenceOriginal X Y Z T z w hz hw x) =
    nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
      (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw x) :=
  nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x

example : nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫
    nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw =
      correspondenceIncidenceToSupportProduct (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw) :=
  nativeExteriorIncidenceToCoefficientQuotient_inclusion X Y Z T z w hz hw

example : nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫
    pullback.fst (pullback.diagonal T.hom)
      (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw) =
        nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _ :=
  nativeExteriorIncidenceToCoefficientQuotient_parameter X Y Z T z w hz hw
