/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support

/-!
# Actual target images under exterior extension

The exterior target map is the actual Cartesian base change of the original
support target projection. Passing to the closed image retains the exact
Cartesian target image. This is geometric support control, not a composition law.
Uses the same native pullback and image mechanisms as the source-image theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {S : Scheme.{u}} (X Y T : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

/-- The target projection is also the actual base change of its original map. -/
theorem exteriorIdentityTarget_isPullback :
    IsPullback (exteriorIdentityTarget X Y T W)
      (pullback.fst (exteriorSupport_sourceProjection X Y W ≫ X.hom) T.hom)
      (pullback.fst Y.hom T.hom) (exteriorSupport_targetProjection X Y W) := by
  apply IsPullback.flip
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback Y.hom T.hom) ?_
    (exteriorIdentityTarget_fst X Y T W).symm
  simpa only [exteriorIdentityTarget_snd, ← exteriorSupport_projection_base X Y W] using
    (IsPullback.of_hasPullback (exteriorSupport_sourceProjection X Y W ≫ X.hom) T.hom)

/-- The target image of the actual support is the literal Cartesian preimage. -/
theorem exteriorIdentityTarget_range :
    Set.range (exteriorIdentityTarget X Y T W) =
      (pullback.fst Y.hom T.hom) ⁻¹' Set.range (exteriorSupport_targetProjection X Y W) := by
  let h := exteriorIdentityTarget_isPullback X Y T W
  rw [← h.isoPullback_hom_fst]
  change Set.range (fun x =>
    (pullback.fst (pullback.fst Y.hom T.hom)
      (exteriorSupport_targetProjection X Y W)) (h.isoPullback.hom x)) = _
  have hh : Function.Surjective h.isoPullback.hom :=
    (Scheme.homeoOfIso h.isoPullback).surjective
  exact (hh.range_comp _).trans (Scheme.Pullback.range_fst _ _)

/-- The actual image factorization recovers the original exterior target map. -/
@[reassoc]
theorem exteriorIdentityImage_toTarget :
    (exteriorIdentityInclusion X Y T W).toImage ≫
      (exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
      exteriorIdentityTarget X Y T W := by
  change (exteriorIdentityInclusion X Y T W).toImage ≫
    (exteriorIdentityInclusion X Y T W).imageι ≫ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact exteriorIdentityInclusion_snd X Y T W

/-- Passing to the actual image ideal preserves exactly the target image. -/
theorem exteriorIdentityImage_target_range [IsFinite (exteriorSupport_sourceProjection X Y W)] :
    Set.range ((exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) =
      (pullback.fst Y.hom T.hom) ⁻¹' Set.range (exteriorSupport_targetProjection X Y W) := by
  let e := exteriorIdentityInclusion X Y T W
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  have hr := e.toImage.surjective.range_comp
    (e.ker.subschemeι ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom)
  change Set.range (e.toImage ≫ e.ker.subschemeι ≫
    pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) = _ at hr
  dsimp only [e] at hr
  rw [← hr, exteriorIdentityImage_toTarget]
  exact exteriorIdentityTarget_range X Y T W

end Stacks.Chow
