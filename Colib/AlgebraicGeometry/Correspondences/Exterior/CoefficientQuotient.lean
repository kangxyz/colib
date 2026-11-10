/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterDiagonal
public import Colib.CategoryTheory.Limits.Shapes.Pullback.CommonParameter

/-!
# The full native coefficient quotient is the original support product times T

All maps below act on the existing integral support schemes. The comparison
preserves both old support coordinates, the common parameter, and the actual
closed inclusion in the exterior support product. The resulting projection is
smooth because it is a base change of `T → Spec k`, regardless of singularities
or nilpotents in the original support product.
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

local notation3 (prettyPrint := false) "a" => nativeExteriorParameter X Y T z hz
local notation3 (prettyPrint := false) "b" => nativeExteriorParameter Y Z T w hw
local notation3 (prettyPrint := false) "f" =>
  exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom
local notation3 (prettyPrint := false) "g" =>
  exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom
local notation3 (prettyPrint := false) "P" =>
  correspondenceSupportProduct (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "p" =>
  nativeExteriorCoefficientParameterPair X Y T z hz Z w hw

/-- Express the very same coefficient product by the two parameter base maps. -/
def nativeExteriorCoefficientBaseIso : P ≅ pullback (a ≫ T.hom) (b ≫ T.hom) :=
  pullback.congrHom (nativeExteriorParameter_target_base X Y T z hz).symm
    (nativeExteriorParameter_source_base Y Z T w hw).symm

/-- The canonical pair map after this harmless change of base-map expressions. -/
abbrev nativeExteriorParameterPairCanonical :=
  pullback.map (a ≫ T.hom) (b ≫ T.hom) T.hom T.hom a b
    (𝟙 (Spec (.of k))) (by simp) (by simp)

@[reassoc]
theorem nativeExteriorCoefficientBaseIso_hom_pair :
    (nativeExteriorCoefficientBaseIso X Y T z hz Z w hw).hom ≫
      nativeExteriorParameterPairCanonical X Y T z hz Z w hw = p := by
  apply pullback.hom_ext <;>
    simp [nativeExteriorCoefficientBaseIso, nativeExteriorParameterPairCanonical,
      nativeExteriorCoefficientParameterPair, pullback.congrHom_hom, pullback.map]

/-- Forget equality of the parameters, retaining the actual coefficient scheme. -/
def nativeExteriorParameterPullbackToCoefficient : pullback a b ⟶ P :=
  pullback.mapDesc a b T.hom ≫ (nativeExteriorCoefficientBaseIso X Y T z hz Z w hw).inv

/-- The exact parameter fiber, without replacing either native support. -/
theorem nativeExteriorParameterPullback_isPullback :
    IsPullback (pullback.fst a b ≫ a)
      (nativeExteriorParameterPullbackToCoefficient X Y T z hz Z w hw)
      (pullback.diagonal T.hom) p := by
  apply (pullback_map_diagonal_isPullback a b T.hom).of_iso
    (Iso.refl _) (Iso.refl _)
    (nativeExteriorCoefficientBaseIso X Y T z hz Z w hw).symm (Iso.refl _)
  · simp
  · simp [nativeExteriorParameterPullbackToCoefficient]
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      ← nativeExteriorCoefficientBaseIso_hom_pair X Y T z hz Z w hw] using
      (Iso.inv_hom_id_assoc (nativeExteriorCoefficientBaseIso X Y T z hz Z w hw)
        (nativeExteriorParameterPairCanonical X Y T z hz Z w hw)).symm

/-- The support pullback over T is the literal parameter-diagonal quotient. -/
def nativeExteriorParameterPullbackIso : pullback a b ≅ Q :=
  (nativeExteriorParameterPullback_isPullback X Y T z hz Z w hw).isoPullback

/-- The first literal exterior support with its original target-side base map. -/
def nativeExteriorFirstTargetProductIso : pullback f T.hom ≅
    (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme :=
  pullback.congrHom (exteriorSupport_projection_base X Y (integralComponentAt z)).symm rfl ≪≫
    nativeExteriorSupportIso X Y T z hz

@[reassoc (attr := simp)]
theorem nativeExteriorFirstTargetProductIso_hom_parameter :
    (nativeExteriorFirstTargetProductIso X Y T z hz).hom ≫ a = pullback.snd f T.hom := by
  simp [nativeExteriorFirstTargetProductIso, nativeExteriorParameter, Category.assoc,
    pullback.congrHom_hom, pullback.map]

/-- Transport both full support factors through their actual native support isomorphisms. -/
def nativeExteriorSupportParameterPullbackIso :
    pullback (pullback.snd f T.hom) (pullback.snd g T.hom) ≅ pullback a b := by
  let m := pullback.map (pullback.snd f T.hom) (pullback.snd g T.hom) a b
    (nativeExteriorFirstTargetProductIso X Y T z hz).hom
    (nativeExteriorSupportIso Y Z T w hw).hom (𝟙 T.left)
    (by simp) (by simp [nativeExteriorParameter])
  have : IsIso (𝟙 T.left) := (Iso.refl T.left).isIso_hom
  have : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso m

/-- The original coefficient support product with one independent common parameter. -/
abbrev nativeExteriorCoefficientQuotientProduct : Scheme.{u} :=
  pullback (pullback.fst f g ≫ f) T.hom

/-- The actual coefficient quotient retains the entire original support product. -/
def nativeExteriorCoefficientQuotientIso :
    nativeExteriorCoefficientQuotientProduct X Y T z Z w ≅ Q :=
  pullbackCommonParameterIso f g T.hom ≪≫
    nativeExteriorSupportParameterPullbackIso X Y T z hz Z w hw ≪≫
    nativeExteriorParameterPullbackIso X Y T z hz Z w hw

@[reassoc (attr := simp)]
theorem nativeExteriorParameterPullbackIso_hom_inclusion :
    (nativeExteriorParameterPullbackIso X Y T z hz Z w hw).hom ≫ j =
      nativeExteriorParameterPullbackToCoefficient X Y T z hz Z w hw :=
  (nativeExteriorParameterPullback_isPullback X Y T z hz Z w hw).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem nativeExteriorParameterPullbackIso_hom_parameter :
    (nativeExteriorParameterPullbackIso X Y T z hz Z w hw).hom ≫
      pullback.fst (pullback.diagonal T.hom) p = pullback.fst a b ≫ a :=
  (nativeExteriorParameterPullback_isPullback X Y T z hz Z w hw).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientBaseIso_inv_fst :
    (nativeExteriorCoefficientBaseIso X Y T z hz Z w hw).inv ≫
      pullback.fst
        ((integralComponentAt
          (X := pullback (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom))
          (nativeExteriorPoint X Y T z hz)).subschemeι ≫
            pullback.snd (pullback.fst X.hom T.hom ≫ X.hom)
              (pullback.fst Y.hom T.hom ≫ Y.hom) ≫ pullback.fst Y.hom T.hom ≫ Y.hom)
        ((integralComponentAt
          (X := pullback (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom))
          (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
            pullback.fst (pullback.fst Y.hom T.hom ≫ Y.hom)
              (pullback.fst Z.hom T.hom ≫ Z.hom) ≫ pullback.fst Y.hom T.hom ≫ Y.hom) =
        pullback.fst (a ≫ T.hom) (b ≫ T.hom) := by
  simp [nativeExteriorCoefficientBaseIso, pullback.congrHom_inv, pullback.map]

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientBaseIso_inv_snd :
    (nativeExteriorCoefficientBaseIso X Y T z hz Z w hw).inv ≫
      pullback.snd
        ((integralComponentAt
          (X := pullback (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom))
          (nativeExteriorPoint X Y T z hz)).subschemeι ≫
            pullback.snd (pullback.fst X.hom T.hom ≫ X.hom)
              (pullback.fst Y.hom T.hom ≫ Y.hom) ≫ pullback.fst Y.hom T.hom ≫ Y.hom)
        ((integralComponentAt
          (X := pullback (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom))
          (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
            pullback.fst (pullback.fst Y.hom T.hom ≫ Y.hom)
              (pullback.fst Z.hom T.hom ≫ Z.hom) ≫ pullback.fst Y.hom T.hom ≫ Y.hom) =
        pullback.snd (a ≫ T.hom) (b ≫ T.hom) := by
  simp [nativeExteriorCoefficientBaseIso, pullback.congrHom_inv, pullback.map]

@[reassoc (attr := simp)]
theorem nativeExteriorSupportParameterPullbackIso_hom_fst :
    (nativeExteriorSupportParameterPullbackIso X Y T z hz Z w hw).hom ≫ pullback.fst a b =
      pullback.fst (pullback.snd f T.hom) (pullback.snd g T.hom) ≫
        (nativeExteriorFirstTargetProductIso X Y T z hz).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorSupportParameterPullbackIso_hom_snd :
    (nativeExteriorSupportParameterPullbackIso X Y T z hz Z w hw).hom ≫ pullback.snd a b =
      pullback.snd (pullback.snd f T.hom) (pullback.snd g T.hom) ≫
        (nativeExteriorSupportIso Y Z T w hw).hom :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientQuotientIso_hom_parameter :
    (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫
      pullback.fst (pullback.diagonal T.hom) p = pullback.snd _ T.hom := by
  simp [nativeExteriorCoefficientQuotientIso, Category.assoc]

@[reassoc (attr := simp)]
theorem nativeExteriorFirstTargetProductIso_hom_old_fst :
    (nativeExteriorFirstTargetProductIso X Y T z hz).hom ≫
      (nativeExteriorSupportIso X Y T z hz).inv ≫
        pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          T.hom = pullback.fst f T.hom := by
  simp [nativeExteriorFirstTargetProductIso, Category.assoc, pullback.congrHom_hom, pullback.map]

/-- The first original support coordinate, including all inclusion and inverse maps. -/
@[reassoc]
theorem nativeExteriorCoefficientQuotientIso_hom_first :
    (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫ j ≫ pullback.fst _ _ ≫
      (nativeExteriorSupportIso X Y T z hz).inv ≫
        pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          T.hom = pullback.fst _ T.hom ≫ pullback.fst f g := by
  simp only [nativeExteriorCoefficientQuotientIso, Iso.trans_hom, Category.assoc,
    SmoothSite.product_hom,
    nativeExteriorParameterPullbackIso_hom_inclusion_assoc,
    nativeExteriorParameterPullbackToCoefficient, nativeExteriorCoefficientBaseIso_inv_fst_assoc,
    pullback.mapDesc, pullback.map, pullback.lift_fst_assoc, Category.comp_id,
    nativeExteriorSupportParameterPullbackIso_hom_fst_assoc,
    nativeExteriorFirstTargetProductIso_hom_old_fst, pullbackCommonParameterIso_hom_first]

/-- The second original support coordinate is preserved by the same isomorphism. -/
@[reassoc]
theorem nativeExteriorCoefficientQuotientIso_hom_second :
    (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫ j ≫ pullback.snd _ _ ≫
      (nativeExteriorSupportIso Y Z T w hw).inv ≫ pullback.fst g T.hom =
        pullback.fst _ T.hom ≫ pullback.snd f g := by
  simp only [nativeExteriorCoefficientQuotientIso, Iso.trans_hom, Category.assoc,
    SmoothSite.product_hom,
    nativeExteriorParameterPullbackIso_hom_inclusion_assoc,
    nativeExteriorParameterPullbackToCoefficient, nativeExteriorCoefficientBaseIso_inv_snd_assoc,
    pullback.mapDesc, pullback.map, pullback.lift_snd_assoc, Category.comp_id,
    nativeExteriorSupportParameterPullbackIso_hom_snd_assoc,
    Iso.hom_inv_id_assoc, pullbackCommonParameterIso_hom_second]

/-- Forget the common parameter after imposing its actual diagonal equations. -/
def nativeExteriorCoefficientQuotientProjection : Q ⟶
    correspondenceSupportProduct X.hom Y.hom Z.hom z w :=
  (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).inv ≫ pullback.fst _ T.hom

instance nativeExteriorCoefficientQuotientProjection_smooth :
    Smooth (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw) := by
  dsimp only [nativeExteriorCoefficientQuotientProjection]
  infer_instance

instance nativeExteriorCoefficientQuotientProjection_flat :
    Flat (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw) := inferInstance

@[reassoc (attr := simp)]
theorem nativeExteriorCoefficientQuotientIso_hom_projection :
    (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom ≫
      nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw = pullback.fst _ T.hom := by
  simp [nativeExteriorCoefficientQuotientProjection]

/-- Projection to the first original support retains the actual native support identification. -/
@[reassoc]
theorem nativeExteriorCoefficientQuotientProjection_fst :
    nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw ≫ pullback.fst f g =
      j ≫ pullback.fst _ _ ≫ (nativeExteriorSupportIso X Y T z hz).inv ≫
        pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          T.hom := by
  apply (cancel_epi (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom).mp
  simp only [nativeExteriorCoefficientQuotientIso_hom_projection_assoc,
    nativeExteriorCoefficientQuotientIso_hom_first]

/-- Projection to the second original support retains the actual native support identification. -/
@[reassoc]
theorem nativeExteriorCoefficientQuotientProjection_snd :
    nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw ≫ pullback.snd f g =
      j ≫ pullback.snd _ _ ≫ (nativeExteriorSupportIso Y Z T w hw).inv ≫ pullback.fst g T.hom := by
  apply (cancel_epi (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom).mp
  simp only [nativeExteriorCoefficientQuotientIso_hom_projection_assoc,
    nativeExteriorCoefficientQuotientIso_hom_second]

/-- This projection is the actual base change of the smooth parameter map. -/
theorem nativeExteriorCoefficientQuotientProjection_isPullback :
    IsPullback (nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw)
      (pullback.fst (pullback.diagonal T.hom) p) (pullback.fst f g ≫ f) T.hom := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).symm rfl ?_
  · apply (cancel_epi (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom).mp
    simp only [nativeExteriorCoefficientQuotientIso_hom_projection_assoc,
      nativeExteriorCoefficientQuotientIso_hom_parameter_assoc]
    exact pullback.condition
  · apply (cancel_epi (nativeExteriorCoefficientQuotientIso X Y T z hz Z w hw).hom).mp
    simp

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/\
  CoefficientQuotient.lean:34-149,257-385"
  "adaptation" "Actual native coefficient quotient isomorphism, both support coordinates \
  and flat projection"]
  nativeExteriorCoefficientQuotientIso nativeExteriorCoefficientQuotientIso_hom_first
  nativeExteriorCoefficientQuotientIso_hom_second nativeExteriorCoefficientQuotientProjection
  nativeExteriorCoefficientQuotientProjection_isPullback

end Stacks.Chow
