/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Products
public import Colib.AlgebraicGeometry.Correspondences.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Actual diagonal-parameter exterior support geometry

Adapted from motivic_source_a6805c4, Correspondences/Exterior/Identity/Basic.lean.
The support is the literal relative product of a native integral closed subscheme
with a smooth parameter. Both target factors use the same parameter point.
This file proves the finite projection and closed immersion of the support.
It does not yet prove component dominance, a cycle operation, or composition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

/-- Original source projection of the native closed subscheme. -/
abbrev exteriorSupport_sourceProjection : W.subscheme ⟶ X.left :=
  W.subschemeι ≫ pullback.fst X.hom Y.hom

/-- Original target projection of the same closed subscheme. -/
abbrev exteriorSupport_targetProjection : W.subscheme ⟶ Y.left :=
  W.subschemeι ≫ pullback.snd X.hom Y.hom

theorem exteriorSupport_projection_base :
    exteriorSupport_sourceProjection X Y W ≫ X.hom =
      exteriorSupport_targetProjection X Y W ≫ Y.hom := by
  simp only [exteriorSupport_sourceProjection, exteriorSupport_targetProjection, Category.assoc,
    pullback.condition]


/-- The genuine exterior support before assigning any cycle. -/
abbrev exteriorIdentitySupport : Scheme.{u} :=
  pullback ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom

/-- Projection of the exterior support onto its source product. -/
def exteriorIdentitySource : (exteriorIdentitySupport X Y T W) ⟶ (SmoothSite.product X T).left :=
  pullback.map _ _ _ _ (exteriorSupport_sourceProjection X Y W) (𝟙 T.left) (𝟙 S)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem exteriorIdentitySource_fst :
    (exteriorIdentitySource X Y T W) ≫ pullback.fst X.hom T.hom =
      pullback.fst ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom ≫
        (exteriorSupport_sourceProjection X Y W) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentitySource_snd :
    (exteriorIdentitySource X Y T W) ≫ pullback.snd X.hom T.hom =
      pullback.snd ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The exterior source projection is the actual base change of the original finite map. -/
theorem exteriorIdentitySource_isPullback :
    IsPullback ((exteriorIdentitySource X Y T W))
      (pullback.fst ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom)
      (pullback.fst X.hom T.hom) (exteriorSupport_sourceProjection X Y W) := by
  apply IsPullback.flip
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback X.hom T.hom) ?_
    ((exteriorIdentitySource_fst X Y T W)).symm
  simpa only [(exteriorIdentitySource_snd X Y T W)] using
    (IsPullback.of_hasPullback ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom)

instance exteriorIdentitySource_isFinite
    [IsFinite (exteriorSupport_sourceProjection X Y W)] :
    IsFinite ((exteriorIdentitySource X Y T W)) :=
  MorphismProperty.of_isPullback ((exteriorIdentitySource_isPullback X Y T W)).flip inferInstance

/-- The target map uses the identical parameter point. -/
def exteriorIdentityTarget : (exteriorIdentitySupport X Y T W) ⟶ (SmoothSite.product Y T).left :=
  pullback.lift
    (pullback.fst ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom ≫
        (exteriorSupport_targetProjection X Y W))
    (pullback.snd ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom)
    (by rw [Category.assoc, ← (exteriorSupport_projection_base X Y W), pullback.condition])

@[reassoc (attr := simp)]
theorem exteriorIdentityTarget_fst :
    (exteriorIdentityTarget X Y T W) ≫ pullback.fst Y.hom T.hom =
      pullback.fst ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom ≫
        (exteriorSupport_targetProjection X Y W) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentityTarget_snd :
    (exteriorIdentityTarget X Y T W) ≫ pullback.snd Y.hom T.hom =
      pullback.snd ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom :=
  pullback.lift_snd _ _ _

/-- The literal diagonal-parameter support map into the correspondence ambient product. -/
def exteriorIdentityInclusion : (exteriorIdentitySupport X Y T W) ⟶
    pullback (SmoothSite.product X T).hom (SmoothSite.product Y T).hom :=
  pullback.lift ((exteriorIdentitySource X Y T W)) ((exteriorIdentityTarget X Y T W)) (by
    simp only [SmoothSite.product_hom, ← Category.assoc,
      exteriorIdentitySource_fst, exteriorIdentityTarget_fst]
    simpa only [Category.assoc] using
      congrArg (pullback.fst ((exteriorSupport_sourceProjection X Y W) ≫ X.hom) T.hom ≫ ·)
        (exteriorSupport_projection_base X Y W))

@[reassoc]
theorem exteriorIdentityInclusion_fst :
    (exteriorIdentityInclusion X Y T W) ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
        (exteriorIdentitySource X Y T W) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentityInclusion_fst_simp :
    (exteriorIdentityInclusion X Y T W) ≫
      pullback.fst (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Y.hom T.hom ≫ Y.hom) =
        (exteriorIdentitySource X Y T W) :=
  exteriorIdentityInclusion_fst X Y T W

@[reassoc]
theorem exteriorIdentityInclusion_snd :
    (exteriorIdentityInclusion X Y T W) ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
        (exteriorIdentityTarget X Y T W) := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorIdentityInclusion_snd_simp :
    (exteriorIdentityInclusion X Y T W) ≫
      pullback.snd (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Y.hom T.hom ≫ Y.hom) =
        (exteriorIdentityTarget X Y T W) :=
  exteriorIdentityInclusion_snd X Y T W

instance exteriorIdentityInclusion_isFinite
    [IsFinite (exteriorSupport_sourceProjection X Y W)] :
    IsFinite ((exteriorIdentityInclusion X Y T W)) := by
  have : IsFinite ((exteriorIdentityInclusion X Y T W) ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) := by
    simpa only [exteriorIdentityInclusion_fst] using
      (inferInstance : IsFinite ((exteriorIdentitySource X Y T W)))
  exact IsFinite.of_comp _ (pullback.fst _ _)

instance exteriorIdentityInclusion_mono : Mono ((exteriorIdentityInclusion X Y T W)) where
  right_cancellation {Z} f g h := by
    have hsource := congrArg
      (fun a => a ≫ pullback.fst (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom) h
    have htarget := congrArg
      (fun a => a ≫ pullback.snd (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom) h
    simp only [Category.assoc, exteriorIdentityInclusion_fst] at hsource
    simp only [Category.assoc, exteriorIdentityInclusion_snd] at htarget
    apply pullback.hom_ext
    · apply (cancel_mono W.subschemeι).mp
      apply pullback.hom_ext
      · simpa only [Category.assoc, exteriorIdentitySource_fst,
          exteriorSupport_sourceProjection] using
          congrArg (fun a => a ≫ pullback.fst X.hom T.hom) hsource
      · simpa only [Category.assoc, exteriorIdentityTarget_fst,
          exteriorSupport_targetProjection] using
          congrArg (fun a => a ≫ pullback.fst Y.hom T.hom) htarget
    · simpa only [Category.assoc, exteriorIdentitySource_snd] using
        congrArg (fun a => a ≫ pullback.snd X.hom T.hom) hsource

@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean:136-166"
  "adaptation" "Actual support closed immersion using native ideal sheaf data"]
instance exteriorIdentityInclusion_isClosedImmersion
    [IsFinite (exteriorSupport_sourceProjection X Y W)] :
    IsClosedImmersion ((exteriorIdentityInclusion X Y T W)) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩


/-- The actual product support is integral for a geometrically integral parameter. -/
instance exteriorIdentitySupport_isIntegral [GeometricallyIntegral T.hom]
    [IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme] :
    IsIntegral (exteriorIdentitySupport X Y T W) :=
  inferInstanceAs (IsIntegral (pullback
    (exteriorSupport_sourceProjection X Y W ≫ X.hom) T.hom))

end Stacks.Chow
