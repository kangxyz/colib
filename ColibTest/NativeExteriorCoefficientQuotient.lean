module

import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientQuotient

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

example : nativeExteriorCoefficientQuotientProduct X Y T z Z w ≅
    nativeExteriorParameterDiagonal X Y T z hz Z w hw :=
  nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw

example : Smooth (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw) :=
  inferInstance

example : (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫
    nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw = pullback.fst _ T.hom :=
  nativeExteriorCoefficientQuotientIso_hom_projection X Y T z hz Z w hw

local notation3 "f" =>
  exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom
local notation3 "g" =>
  exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom
local notation3 "j" => nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 "p" => nativeExteriorCoefficientParameterPair X Y T z hz Z w hw

example : (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫
    pullback.fst (pullback.diagonal T.hom) p = pullback.snd _ T.hom :=
  nativeExteriorCoefficientQuotientIso_hom_parameter X Y T z hz Z w hw

example : (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫ j ≫
    pullback.fst _ _ ≫ (nativeExteriorSupportIso X Y T z hz).inv ≫
      pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        T.hom = pullback.fst _ T.hom ≫ pullback.fst f g :=
  nativeExteriorCoefficientQuotientIso_hom_first X Y T z hz Z w hw

example : (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫ j ≫
    pullback.snd _ _ ≫ (nativeExteriorSupportIso Y Z T w hw).inv ≫ pullback.fst g T.hom =
      pullback.fst _ T.hom ≫ pullback.snd f g :=
  nativeExteriorCoefficientQuotientIso_hom_second X Y T z hz Z w hw

example : IsPullback (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw)
    (pullback.fst (pullback.diagonal T.hom) p) (pullback.fst f g ≫ f) T.hom :=
  nativeExteriorCoefficientQuotientProjection_isPullback X Y T z hz Z w hw

example : Flat (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw) :=
  inferInstance
