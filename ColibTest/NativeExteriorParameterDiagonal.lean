module

import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterDiagonal

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

example : Flat (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw) := inferInstance

example : IsClosedImmersion (nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw) :=
  inferInstance

example : IsPullback
    (pullback.fst (pullback.diagonal T.hom)
      (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw))
    (nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw)
    (pullback.diagonal T.hom) (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw) :=
  nativeExteriorParameterDiagonal_isPullback X Y T z hz Z w hw

example : nativeExteriorParameter X Y T z hz =
    (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
        pullback.snd X.hom T.hom :=
  nativeExteriorParameter_eq_source_snd X Y T z hz

example : nativeExteriorParameter X Y T z hz =
    (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
        pullback.snd Y.hom T.hom :=
  nativeExteriorParameter_eq_target_snd X Y T z hz

example : nativeExteriorCoefficientParameterPair X Y T z hz Z w hw ≫
    pullback.fst T.hom T.hom = pullback.fst _ _ ≫ nativeExteriorParameter X Y T z hz :=
  nativeExteriorCoefficientParameterPair_fst X Y T z hz Z w hw

example : nativeExteriorCoefficientParameterPair X Y T z hz Z w hw ≫
    pullback.snd T.hom T.hom = pullback.snd _ _ ≫ nativeExteriorParameter Y Z T w hw :=
  nativeExteriorCoefficientParameterPair_snd X Y T z hz Z w hw
