/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport
public import Colib.AlgebraicGeometry.Correspondences.Composition.Diagonal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The actual parameter-diagonal quotient of native exterior coefficients

The coefficient scheme is the existing product of the two native integral
supports. Its two actual parameter projections define a flat map to `T ×[k] T`.
The quotient below is the literal pullback of the parameter diagonal, with its
full closed subscheme structure. In particular no reduction is taken and no
flatness of either correspondence over its source or target is assumed.
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

/-- The actual parameter of the native exterior integral support. -/
abbrev nativeExteriorParameter :
    (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme ⟶ T.left :=
  (nativeExteriorSupportIso X Y T z hz).inv ≫
    pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) T.hom

/-- Parameter flatness uses only the map of the original support to the field. -/
instance nativeExteriorParameter_flat : Flat (nativeExteriorParameter X Y T z hz) := by
  let : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  have : Flat (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) :=
    Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
      (Y := Spec (.of k)) _
  dsimp only [nativeExteriorParameter]
  infer_instance

/-- The source and target of this support have exactly the same parameter. -/
@[reassoc]
theorem nativeExteriorParameter_eq_source_snd :
    nativeExteriorParameter X Y T z hz =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          pullback.snd X.hom T.hom := by
  simpa only [Category.assoc, exteriorIdentitySource_snd, nativeExteriorParameter] using
    congrArg (fun m => m ≫ pullback.snd X.hom T.hom)
      (nativeExteriorSupportIso_inv_source X Y T z hz)

@[reassoc]
theorem nativeExteriorParameter_eq_target_snd :
    nativeExteriorParameter X Y T z hz =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          pullback.snd Y.hom T.hom := by
  simpa only [Category.assoc, exteriorIdentityTarget_snd, nativeExteriorParameter] using
    congrArg (fun m => m ≫ pullback.snd Y.hom T.hom)
      (nativeExteriorSupportIso_inv_target X Y T z hz)

@[reassoc]
theorem nativeExteriorParameter_source_base :
    nativeExteriorParameter X Y T z hz ≫ T.hom =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          (SmoothSite.product X T).hom := by
  rw [nativeExteriorParameter_eq_source_snd]
  simp only [Category.assoc, SmoothSite.product_hom, pullback.condition]

@[reassoc]
theorem nativeExteriorParameter_target_base :
    nativeExteriorParameter X Y T z hz ≫ T.hom =
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          (SmoothSite.product Y T).hom := by
  rw [nativeExteriorParameter_eq_target_snd]
  simp only [Category.assoc, SmoothSite.product_hom, pullback.condition]

variable (Z : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

/-- The actual product of exterior supports, with its two parameter coordinates. -/
def nativeExteriorCoefficientParameterPair :
    correspondenceSupportProduct (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
      (nativeExteriorPoint Y Z T w hw) ⟶ pullback T.hom T.hom :=
  pullback.map _ _ T.hom T.hom (nativeExteriorParameter X Y T z hz)
    (nativeExteriorParameter Y Z T w hw) (𝟙 (Spec (.of k)))
    (by simpa using (nativeExteriorParameter_target_base X Y T z hz).symm)
    (by simpa using (nativeExteriorParameter_source_base Y Z T w hw).symm)

instance nativeExteriorCoefficientParameterPair_flat :
    Flat (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw) := by
  unfold nativeExteriorCoefficientParameterPair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (nativeExteriorParameter X Y T z hz)))
    (inferInstanceAs (Flat (nativeExteriorParameter Y Z T w hw)))
    (nativeExteriorParameter_target_base X Y T z hz).symm
    (nativeExteriorParameter_source_base Y Z T w hw).symm

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientParameterPair_fst :
    nativeExteriorCoefficientParameterPair X Y T z hz Z w hw ≫ pullback.fst T.hom T.hom =
      pullback.fst _ _ ≫ nativeExteriorParameter X Y T z hz :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientParameterPair_snd :
    nativeExteriorCoefficientParameterPair X Y T z hz Z w hw ≫ pullback.snd T.hom T.hom =
      pullback.snd _ _ ≫ nativeExteriorParameter Y Z T w hw :=
  pullback.lift_snd _ _ _

/-- Impose exactly equality of the two actual coefficient parameters. -/
abbrev nativeExteriorParameterDiagonal : Scheme.{u} :=
  pullback (pullback.diagonal T.hom)
    (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw)

/-- The complete scheme-theoretic parameter-diagonal inclusion. -/
abbrev nativeExteriorParameterDiagonalInclusion :
    nativeExteriorParameterDiagonal X Y T z hz Z w hw ⟶
      correspondenceSupportProduct (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
        (nativeExteriorPoint Y Z T w hw) :=
  pullback.snd (pullback.diagonal T.hom)
    (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw)

instance nativeExteriorParameterDiagonalInclusion_isClosedImmersion :
    IsClosedImmersion (nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw) :=
  inferInstance

/-- The actual Cartesian square used to transport the parameter equations. -/
theorem nativeExteriorParameterDiagonal_isPullback :
    IsPullback (pullback.fst (pullback.diagonal T.hom)
      (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw))
      (nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw)
      (pullback.diagonal T.hom) (nativeExteriorCoefficientParameterPair X Y T z hz Z w hw) :=
  IsPullback.of_hasPullback _ _

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/ParameterDiagonal.lean:36-122"
  "adaptation" "Actual native exterior support product, flat parameter pair and \
  unreduced diagonal quotient"]
  nativeExteriorParameter nativeExteriorParameter_flat nativeExteriorCoefficientParameterPair
  nativeExteriorCoefficientParameterPair_flat nativeExteriorParameterDiagonal
  nativeExteriorParameterDiagonal_isPullback

end Stacks.Chow
