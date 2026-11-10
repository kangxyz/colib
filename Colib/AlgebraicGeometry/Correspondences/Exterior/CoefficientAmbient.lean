/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientParameterQuotient
public import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientQuotient

/-!
# The actual coefficient quotient inside the ambient parameter quotient

The parameter quotient of the existing native support product is the Cartesian
inverse image of the ambient parameter quotient. Both remaining middle
coordinates agree with the flat projection to the original support product.
This statement retains scheme structure and actual morphisms; it asserts no
regularity for the remaining equations on the correspondence supports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (Z : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "p" =>
  nativeExteriorCoefficientParameterPair X Y T z hz Z w hw
local notation3 (prettyPrint := false) "i" =>
  correspondenceSupportProductInclusion (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw

/-- The coefficient parameter pair is induced by the actual ambient parameter pair. -/
@[reassoc]
theorem nativeExteriorCoefficientParameterPair_ambient :
    i ≫ exteriorAmbientParameterPair X Y Z T = p := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorAmbientParameterPair_fst,
      correspondenceSupportProductInclusion_fst_assoc,
      nativeExteriorCoefficientParameterPair_fst, nativeExteriorParameter_eq_target_snd]
  · simp only [Category.assoc, exteriorAmbientParameterPair_snd,
      correspondenceSupportProductInclusion_snd_assoc,
      nativeExteriorCoefficientParameterPair_snd, nativeExteriorParameter_eq_source_snd]

/-- The actual native coefficient quotient maps into the ambient parameter quotient. -/
def nativeExteriorCoefficientQuotientInclusion : Q ⟶ exteriorAmbientParameterQuotient X Y Z T :=
  pullback.lift (pullback.fst (pullback.diagonal T.hom) p) (j ≫ i) (by
    rw [Category.assoc, nativeExteriorCoefficientParameterPair_ambient X Y T z hz Z w hw]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientQuotientInclusion_parameter :
    nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw ≫
      pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T) =
        pullback.fst (pullback.diagonal T.hom) p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientQuotientInclusion_ambient :
    nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw ≫
      exteriorAmbientParameterInclusion X Y Z T = j ≫ i :=
  pullback.lift_snd _ _ _

/-- The support and ambient parameter quotients form the literal Cartesian square. -/
theorem nativeExteriorCoefficientQuotientInclusion_isPullback :
    IsPullback (nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw) j
      (exteriorAmbientParameterInclusion X Y Z T) i := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T))
    (h₂₂ := exteriorAmbientParameterPair X Y Z T)
  · simpa only [nativeExteriorCoefficientQuotientInclusion_parameter,
      nativeExteriorCoefficientParameterPair_ambient] using
        nativeExteriorParameterDiagonal_isPullback X Y T z hz Z w hw
  · exact nativeExteriorCoefficientQuotientInclusion_ambient X Y T z hz Z w hw
  · exact exteriorAmbientParameter_isPullback X Y Z T

instance nativeExteriorCoefficientQuotientInclusion_isClosedImmersion :
    IsClosedImmersion (nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw) :=
  MorphismProperty.of_isPullback
    (nativeExteriorCoefficientQuotientInclusion_isPullback X Y T z hz Z w hw).flip
    inferInstance

/-- The original coefficient product retains its two original middle coordinates. -/
def nativeOriginalCoefficientMiddlePair :
    correspondenceSupportProduct X.hom Y.hom Z.hom z w ⟶ pullback Y.hom Y.hom :=
  correspondenceSupportProductInclusion X.hom Y.hom Z.hom z w ≫
    correspondenceMiddlePair X.hom Y.hom Z.hom

@[reassoc (attr := simp)]
theorem nativeOriginalCoefficientMiddlePair_fst :
    nativeOriginalCoefficientMiddlePair X Y z Z w ≫ pullback.fst Y.hom Y.hom =
      pullback.fst
        (exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
        (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom) ≫
          exteriorSupportTargetProjection X Y (integralComponentAt z) := by
  simp [nativeOriginalCoefficientMiddlePair, correspondenceMiddlePair, pullback.map,
    exteriorSupportTargetProjection, Category.assoc]
  dsimp only [exteriorSupportSourceProjection, exteriorSupportTargetProjection]
  congr 2

@[reassoc (attr := simp)]
theorem nativeOriginalCoefficientMiddlePair_snd :
    nativeOriginalCoefficientMiddlePair X Y z Z w ≫ pullback.snd Y.hom Y.hom =
      pullback.snd
        (exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
        (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom) ≫
          exteriorSupportSourceProjection Y Z (integralComponentAt w) := by
  simp [nativeOriginalCoefficientMiddlePair, correspondenceMiddlePair, pullback.map,
    exteriorSupportSourceProjection, Category.assoc]
  dsimp only [exteriorSupportSourceProjection, exteriorSupportTargetProjection]
  congr 2

/-- The native support isomorphism retains the first original middle coordinate. -/
@[reassoc]
theorem nativeExteriorSupportIso_inv_old_target :
    (nativeExteriorSupportIso X Y T z hz).inv ≫
      pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) T.hom ≫
        exteriorSupportTargetProjection X Y (integralComponentAt z) =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          pullback.fst Y.hom T.hom := by
  simpa only [Category.assoc, exteriorIdentityTarget_fst] using
    congrArg (fun m => m ≫ pullback.fst Y.hom T.hom)
      (nativeExteriorSupportIso_inv_target X Y T z hz)

/-- The native support isomorphism retains the second original middle coordinate. -/
@[reassoc]
theorem nativeExteriorSupportIso_inv_old_source :
    (nativeExteriorSupportIso X Y T z hz).inv ≫
      pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) T.hom ≫
        exteriorSupportSourceProjection X Y (integralComponentAt z) =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          pullback.fst X.hom T.hom := by
  simpa only [Category.assoc, exteriorIdentitySource_fst] using
    congrArg (fun m => m ≫ pullback.fst X.hom T.hom)
      (nativeExteriorSupportIso_inv_source X Y T z hz)

/-- Both remaining middle coordinates agree with the actual original coefficient projection. -/
@[reassoc]
theorem nativeExteriorCoefficientQuotientInclusion_remainingPair :
    nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw ≫
      exteriorAmbientRemainingPair X Y Z T = q ≫ nativeOriginalCoefficientMiddlePair X Y z Z w := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorAmbientRemainingPair_fst,
      nativeExteriorCoefficientQuotientInclusion_ambient_assoc,
      correspondenceSupportProductInclusion_fst_assoc, nativeOriginalCoefficientMiddlePair_fst,
      nativeExteriorCoefficientQuotientProjection_fst_assoc,
      nativeExteriorSupportIso_inv_old_target]
  · simp only [Category.assoc, exteriorAmbientRemainingPair_snd,
      nativeExteriorCoefficientQuotientInclusion_ambient_assoc,
      correspondenceSupportProductInclusion_snd_assoc, nativeOriginalCoefficientMiddlePair_snd,
      nativeExteriorCoefficientQuotientProjection_snd_assoc,
      nativeExteriorSupportIso_inv_old_source]

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/CoefficientAmbient.lean:37-132"
  "adaptation" "Actual native coefficient inclusion in the ambient parameter quotient, \
  its Cartesian square, and equality of both remaining original middle coordinates"]
  nativeExteriorCoefficientParameterPair_ambient nativeExteriorCoefficientQuotientInclusion
  nativeExteriorCoefficientQuotientInclusion_parameter
  nativeExteriorCoefficientQuotientInclusion_ambient
  nativeExteriorCoefficientQuotientInclusion_isPullback
  nativeExteriorCoefficientQuotientInclusion_remainingPair

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/RemainingPair.lean:37-120"
  "adaptation" "Original coefficient middle pair and exact old coordinates through \
  the native integral-support isomorphisms"]
  nativeOriginalCoefficientMiddlePair nativeExteriorSupportIso_inv_old_target
  nativeExteriorSupportIso_inv_old_source

end Stacks.Chow
