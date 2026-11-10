module

import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientAmbient
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

local notation3 "j" => nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 "α" => nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw
local notation3 "q" => nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 "i" => correspondenceSupportProductInclusion
  (SmoothSite.product X T).hom (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
  (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)

example : IsPullback α j (exteriorAmbientParameterInclusion X Y Z T) i :=
  nativeExteriorCoefficientQuotientInclusion_isPullback X Y T z hz Z w hw

example : IsClosedImmersion α := inferInstance

/-- The Cartesian square identifies the actual coefficient parameter ideal. -/
example : (j).ker = (exteriorAmbientParameterInclusion X Y Z T).ker.comap i := by
  let sq := (nativeExteriorCoefficientQuotientInclusion_isPullback X Y T z hz Z w hw).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The target-side original middle coordinate survives on the full coefficient quotient. -/
example : α ≫ exteriorAmbientRemainingPair X Y Z T ≫ pullback.fst Y.hom Y.hom =
    q ≫ pullback.fst
      (exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
      (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom) ≫
        exteriorSupportTargetProjection X Y (integralComponentAt z) := by
  rw [nativeExteriorCoefficientQuotientInclusion_remainingPair_assoc]
  exact congrArg (fun m => q ≫ m) (nativeOriginalCoefficientMiddlePair_fst X Y z Z w)

/-- The source-side original middle coordinate survives on the same quotient. -/
example : α ≫ exteriorAmbientRemainingPair X Y Z T ≫ pullback.snd Y.hom Y.hom =
    q ≫ pullback.snd
      (exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
      (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom) ≫
        exteriorSupportSourceProjection Y Z (integralComponentAt w) := by
  rw [nativeExteriorCoefficientQuotientInclusion_remainingPair_assoc]
  exact congrArg (fun m => q ≫ m) (nativeOriginalCoefficientMiddlePair_snd X Y z Z w)

/-- The actual native exterior incidence uses precisely the same original middle pair. -/
example : nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫
    α ≫ exteriorAmbientRemainingPair X Y Z T =
      nativeExteriorIncidenceOriginal X Y Z T z w hz hw ≫
        correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w ≫
          nativeOriginalCoefficientMiddlePair X Y z Z w := by
  rw [nativeExteriorCoefficientQuotientInclusion_remainingPair,
    nativeExteriorIncidenceToCoefficientQuotient_projection_assoc]
