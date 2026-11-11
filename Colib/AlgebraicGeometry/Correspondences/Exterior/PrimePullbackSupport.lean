/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralPullback
public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidencePushforwardSquare

/-!
# The actual prime exterior support as an inverse image

The product of the original integral support with one parameter maps into
`(X × Y) × T`. This is the literal base change of the original closed immersion.
Its composite with the existing common-parameter diagonal is the existing
`exteriorIdentityInclusion`. The resulting comparison identifies the unique
inverse-image generic with the existing `nativeExteriorPoint`.

The native prime is not redefined. The only degree-one factors here are actual
closed immersions. There is no claim that the parameter-forgetting projection
has degree one, nor any properness assertion for an ambient projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

section Base

variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

/-- Base change of the actual closed support into the one-parameter outer product. -/
def exteriorSupportToOuterProduct : exteriorIdentitySupport X Y T W ⟶
    exteriorOuterProduct X Y T :=
  pullback.lift
    (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫ W.subschemeι)
    (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)
    (by simpa only [exteriorSupportSourceProjection, Category.assoc] using
      (pullback.condition
        (f := exteriorSupportSourceProjection X Y W ≫ X.hom) (g := T.hom)))

@[reassoc (attr := simp)]
theorem exteriorSupportToOuterProduct_fst :
    exteriorSupportToOuterProduct X Y T W ≫
      pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom =
        pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫
          W.subschemeι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorSupportToOuterProduct_snd :
    exteriorSupportToOuterProduct X Y T W ≫
      pullback.snd (pullback.fst X.hom Y.hom ≫ X.hom) T.hom =
        pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom :=
  pullback.lift_snd _ _ _

/-- The literal support product is the actual scheme-theoretic inverse image. -/
theorem exteriorSupportToOuterProduct_isPullback :
    IsPullback (exteriorSupportToOuterProduct X Y T W)
      (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)
      (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom) W.subschemeι := by
  have hp : IsPullback
      (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)
      (exteriorSupportToOuterProduct X Y T W ≫
        pullback.snd (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)
      (W.subschemeι ≫ (pullback.fst X.hom Y.hom ≫ X.hom)) T.hom := by
    simpa only [exteriorSupportToOuterProduct_snd,
      exteriorSupportSourceProjection, Category.assoc] using
      (IsPullback.of_hasPullback (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)
  exact (hp.of_bot (exteriorSupportToOuterProduct_fst X Y T W).symm
    (IsPullback.of_hasPullback (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)).flip

instance exteriorSupportToOuterProduct_isClosedImmersion :
    IsClosedImmersion (exteriorSupportToOuterProduct X Y T W) :=
  MorphismProperty.of_isPullback
    (exteriorSupportToOuterProduct_isPullback X Y T W).flip inferInstance

/-- The comparison to the actual comap subscheme, preserving its ambient inclusion. -/
def exteriorSupportComapIso : exteriorIdentitySupport X Y T W ≅
    (W.comap (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)).subscheme :=
  (exteriorSupportToOuterProduct_isPullback X Y T W).isoPullback ≪≫
    (W.comapIso (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)).symm

@[reassoc]
theorem exteriorSupportComapIso_hom_inclusion :
    (exteriorSupportComapIso X Y T W).hom ≫
      (W.comap (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)).subschemeι =
        exteriorSupportToOuterProduct X Y T W := by
  simp only [exteriorSupportComapIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι]
  exact (exteriorSupportToOuterProduct_isPullback X Y T W).isoPullback_hom_fst

/-- Both maps repeat the same parameter, and agree as scheme morphisms. -/
@[reassoc]
theorem exteriorSupportToOuterProduct_diagonal :
    exteriorSupportToOuterProduct X Y T W ≫ exteriorOuterDiagonal X Y T =
      exteriorIdentityInclusion X Y T W := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [exteriorOuterDiagonal, exteriorSupportToOuterProduct,
        exteriorIdentityInclusion, exteriorIdentitySource, exteriorSupportSourceProjection,
        Category.assoc]
  · apply pullback.hom_ext <;>
      simp [exteriorOuterDiagonal, exteriorSupportToOuterProduct,
        exteriorIdentityInclusion, exteriorIdentityTarget, exteriorSupportTargetProjection,
        Category.assoc]

end Base

private theorem iso_hom_genericPoint {A B : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] (e : A ≅ B) :
    e.hom (genericPoint A) = genericPoint B := by
  have h := (genericPointsIso e
    ⟨genericPoint A, genericPoint_mem_genericPoints A⟩).property
  change e.hom (genericPoint A) ∈ genericPoints B at h
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h

section Field

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation3 (prettyPrint := false) "π" =>
  (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)

local instance : IsLocallyNoetherian (pullback (C := Scheme) X.hom Y.hom) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (show pullback X.hom Y.hom ⟶ Spec (.of k) from pullback.fst X.hom Y.hom ≫ X.hom)

/-- The inverse-image generic is the image of the literal support-product generic. -/
theorem exteriorSupportToOuterProduct_genericPoint :
    let := nativeExteriorSupport_isIntegral X Y T z hz
    exteriorSupportToOuterProduct X Y T (integralComponentAt z)
        (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z))) =
      geometricallyIntegralPullbackPoint π z := by
  let := nativeExteriorSupport_isIntegral X Y T z hz
  let := isIntegral_comap_integralComponentAt π z
  let e := exteriorSupportComapIso X Y T (integralComponentAt z)
  have h := congrArg
    (fun a : exteriorIdentitySupport X Y T (integralComponentAt z) ⟶
      exteriorOuterProduct X Y T =>
        a (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z))))
    (exteriorSupportComapIso_hom_inclusion X Y T (integralComponentAt z))
  rw [Scheme.Hom.comp_apply, iso_hom_genericPoint e] at h
  exact h.symm

/-- The literal support inclusion sends its generic to the already defined native point. -/
theorem exteriorIdentityInclusion_genericPoint :
    let := nativeExteriorSupport_isIntegral X Y T z hz
    exteriorIdentityInclusion X Y T (integralComponentAt z)
        (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z))) =
      nativeExteriorPoint X Y T z hz := by
  let := nativeExteriorSupport_isIntegral X Y T z hz
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let e := exteriorIdentityInclusion X Y T (integralComponentAt z)
  let : IsIntegral e.ker.subscheme := nativeExteriorImage_isIntegral X Y T z hz
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  have h := congrArg
    (fun a : exteriorIdentitySupport X Y T (integralComponentAt z) ⟶
      pullback (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =>
        a (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z))))
    (Scheme.Hom.toImage_imageι e)
  rw [Scheme.Hom.comp_apply] at h
  have hg := iso_hom_genericPoint (asIso e.toImage)
  change e.toImage (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z))) =
    genericPoint e.ker.subscheme at hg
  rw [hg] at h
  exact h.symm

/-- The actual common-parameter diagonal takes the true pullback generic to the
existing exterior prime point. This is an equality of actual scheme points. -/
theorem exteriorOuterDiagonal_pullbackPoint :
    exteriorOuterDiagonal X Y T (geometricallyIntegralPullbackPoint π z) =
      nativeExteriorPoint X Y T z hz := by
  let := nativeExteriorSupport_isIntegral X Y T z hz
  rw [← exteriorSupportToOuterProduct_genericPoint X Y T z hz]
  change (exteriorSupportToOuterProduct X Y T (integralComponentAt z) ≫
    exteriorOuterDiagonal X Y T) (genericPoint _) = _
  rw [exteriorSupportToOuterProduct_diagonal]
  exact exteriorIdentityInclusion_genericPoint X Y T z hz

/-- Degree one belongs to the actual diagonal closed immersion, not the flat projection. -/
theorem exteriorOuterDiagonal_pullbackPoint_residueDegree :
    (exteriorOuterDiagonal X Y T).residueDegree
      (geometricallyIntegralPullbackPoint π z) = 1 :=
  residueDegree_eq_one_of_isClosedImmersion _ _

end Field

end Stacks.Chow
