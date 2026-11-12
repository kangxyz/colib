/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Geometry


/-! # Literal parameter permutation for the projected zero-section boundary -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Contraction/ProjectionGeometry.lean`, blob
`700588ec732369a67646a9cb624b66632b4a45be`.
Only original neighborhood/projection geometry is extracted. Parameter-permutation geometry is a
separate independent leaf; it is not needed for the actual canonical boundary projection square.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

open CategoryTheory.Limits

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

local notation "X₁" => Functor.obj affineLineCylinder X
local notation "π" =>
  NatTrans.app (projection (SmoothSite.additiveGroupObject (Spec (CommRingCat.of k)))) X
local notation "p" => affineLineCylinder.map π
local notation "q" => torusCylinder.map π
local notation "j₀" => NatTrans.app openInclusion X
local notation "j₁" => NatTrans.app openInclusion X₁
local notation "i₀" => nativeAffineSection (CommRingCat.of k) X 0
local notation "i₁" => nativeAffineSection (CommRingCat.of k) X₁ 0

/-- The iterated actual pullbacks in the zero-section projection square agree.
This is an isomorphism of neighborhood functors, not of coefficient inverse images. -/
def contractionZeroProjectionBaseChangeIso :
    baseChange (i₀).left ⋙ baseChange (π).left ≅ baseChange (p).left ⋙ baseChange (i₁).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (π).left (i₀).left (fg := (i₁ ≫ p).left)
      (hfg := congrArg (fun f ↦ f.left)
        (nativeAffineSection_naturality (.of k) π 0))).symm ≪≫
    MorphismProperty.Over.pullbackComp (i₁).left (p).left

/-- The iterated actual pullbacks in the punctured projection square agree. -/
def contractionPunctureProjectionBaseChangeIso :
    baseChange (p).left ⋙ baseChange (j₁).left ≅ baseChange (j₀).left ⋙ baseChange (q).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (j₁).left (p).left).symm ≪≫
    MorphismProperty.Over.pullbackComp (q).left (j₀).left (fg := (j₁ ≫ p).left)
      (hfg := by
        have h : q ≫ j₀ = j₁ ≫ p := openInclusion.naturality π
        exact (congrArg (fun f ↦ f.left) h).symm)

/-- The zero comparison retains the original ambient-neighborhood projection. -/
@[reassoc (attr := simp)]
theorem contractionZeroProjectionBaseChangeIso_fst
    (E : EtaleSeparatedFiniteType (X₁).left) :
    ((contractionZeroProjectionBaseChangeIso X).hom.app E).left ≫
        pullback.fst (pullback.snd E.hom (p).left) (i₁).left ≫ pullback.fst E.hom (p).left =
      pullback.fst (pullback.snd E.hom (i₀).left) (π).left ≫ pullback.fst E.hom (i₀).left := by
  simp only [contractionZeroProjectionBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, MorphismProperty.Comma.comp_left, Category.assoc,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]
  erw [pullbackLeftPullbackSndIso_inv_fst E.hom (p).left (i₁).left]
  simp only [pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The punctured comparison retains the original ambient-neighborhood projection. -/
@[reassoc (attr := simp)]
theorem contractionPunctureProjectionBaseChangeIso_fst
    (E : EtaleSeparatedFiniteType (X₁).left) :
    ((contractionPunctureProjectionBaseChangeIso X).hom.app E).left ≫
        pullback.fst (pullback.snd E.hom (j₀).left) (q).left ≫ pullback.fst E.hom (j₀).left =
      pullback.fst (pullback.snd E.hom (p).left) (j₁).left ≫ pullback.fst E.hom (p).left := by
  simp only [contractionPunctureProjectionBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, MorphismProperty.Comma.comp_left, Category.assoc,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]
  erw [pullbackLeftPullbackSndIso_inv_fst E.hom (j₀).left (q).left]
  simp only [pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The original base-changed test projects over the original test morphism. -/
theorem projectionRestriction_toBase (V : EtaleSeparatedFiniteType X.left) :
    (restrictionProjection (π)).app V ≫ toBase X V =
      toBase (X₁)
          ((baseChange (π).left).obj V) ≫
        π := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

/-- A target cylinder neighborhood maps into the actual ambient pullback of the
source cylinder. The construction uses the original projection and needs no
replacement of an inverse-image coefficient sheaf. -/
def cylinderProjectionLift (V : EtaleSeparatedFiniteType X.left) :
    (cylinderNeighborhood (X₁)).obj
        ((baseChange (π).left).obj V) ⟶
      (baseChange (p).left).obj ((cylinderNeighborhood X).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (affineLineCylinder.map
        ((restrictionProjection (π)).app V)).left
      ((cylinderNeighborhood (X₁)).obj
        ((baseChange (π).left).obj V)).hom (by
          change (affineLineCylinder.map
              ((restrictionProjection (π)).app V) ≫
            affineLineCylinder.map (toBase X V)).left =
              (affineLineCylinder.map
                (toBase (X₁)
                  ((baseChange (π).left).obj V)) ≫
                affineLineCylinder.map π).left
          rw [← Functor.map_comp, ← Functor.map_comp, projectionRestriction_toBase]))
    (pullback.lift_snd _ _ _)

/-- The displayed lift keeps the literal original ambient-cylinder projection. -/
@[reassoc (attr := simp)]
theorem cylinderProjectionLift_fst (V : EtaleSeparatedFiniteType X.left) :
    (cylinderProjectionLift X V).left ≫
        pullback.fst ((cylinderNeighborhood X).obj V).hom
          (p).left =
      (affineLineCylinder.map
        ((restrictionProjection (π)).app V)).left :=
  pullback.lift_fst _ _ _

/-- The original Laurent representative pulls back through the actual ambient
square by the literal product of the base projection with the identity on `Gₘ`. -/
theorem puncturedProjection_projection (V : EtaleSeparatedFiniteType X.left) :
    (toSmoothSite (torusCylinder.obj X₁)).map
        ((baseChange (j₁).left).map (cylinderProjectionLift X V)) ≫
      (toSmoothSite (torusCylinder.obj X₁)).map
        ((contractionPunctureProjectionBaseChangeIso X).hom.app
          ((cylinderNeighborhood X).obj V)) ≫
      (restrictionProjection q).app ((puncturedNeighborhood X).obj V) ≫
      puncturedProjection X V =
    puncturedProjection X₁ ((baseChange (π).left).obj V) ≫
      SmoothSite.productMap ((restrictionProjection π).app V)
        (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) := by
  apply (cancel_mono
    (openInclusion.app ((toSmoothSite X).obj V))).mp
  simp only [Category.assoc]
  have hn :
      SmoothSite.productMap ((restrictionProjection π).app V)
          (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) ≫
        openInclusion.app ((toSmoothSite X).obj V) =
      openInclusion.app ((toSmoothSite X₁).obj ((baseChange (π).left).obj V)) ≫
        affineLineCylinder.map ((restrictionProjection π).app V) :=
    openInclusion.naturality ((restrictionProjection π).app V)
  rw [puncturedProjection_open, hn,
    ← Category.assoc (puncturedProjection X₁ ((baseChange (π).left).obj V))]
  erw [puncturedProjection_open X₁ ((baseChange (π).left).obj V)]
  apply MorphismProperty.Over.Hom.ext
  change ((baseChange (j₁).left).map (cylinderProjectionLift X V)).left ≫
      ((contractionPunctureProjectionBaseChangeIso X).hom.app
        ((cylinderNeighborhood X).obj V)).left ≫
        pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (j₀).left) (q).left ≫
        pullback.fst ((cylinderNeighborhood X).obj V).hom (j₀).left ≫ 𝟙 _ =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom (j₁).left ≫
      𝟙 _ ≫ (affineLineCylinder.map ((restrictionProjection π).app V)).left
  simp only [Category.comp_id, Category.id_comp]
  rw [contractionPunctureProjectionBaseChangeIso_fst]
  have hmap : ((baseChange (j₁).left).map (cylinderProjectionLift X V)).left ≫
      pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
        (j₁).left =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom
      (j₁).left ≫ (cylinderProjectionLift X V).left :=
    pullback.lift_fst _ _ _
  change ((baseChange (j₁).left).map (cylinderProjectionLift X V)).left ≫
      pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
        (j₁).left ≫ pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom (j₁).left ≫
      (affineLineCylinder.map ((restrictionProjection π).app V)).left
  rw [← Category.assoc, hmap, Category.assoc, cylinderProjectionLift_fst]

/-- Pulling the original zero lift through the actual square is the target
zero lift followed by the ambient cylinder comparison. -/
theorem zeroNeighborhoodLift_projection (V : EtaleSeparatedFiniteType X.left) :
    (baseChange (π).left).map (zeroNeighborhoodLift X V) ≫
        (contractionZeroProjectionBaseChangeIso X).hom.app ((cylinderNeighborhood X).obj V) =
      zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V) ≫
        (baseChange (i₁).left).map (cylinderProjectionLift X V) := by
  let f := (baseChange (π).left).map (zeroNeighborhoodLift X V) ≫
    (contractionZeroProjectionBaseChangeIso X).hom.app ((cylinderNeighborhood X).obj V)
  let g := zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V) ≫
    (baseChange (i₁).left).map (cylinderProjectionLift X V)
  have hmap₀ : ((baseChange (π).left).map (zeroNeighborhoodLift X V)).left ≫
      pullback.fst ((zeroNeighborhood X).obj V).hom (π).left =
    pullback.fst V.hom (π).left ≫ (zeroNeighborhoodLift X V).left :=
    pullback.lift_fst _ _ _
  have hmap₁ : ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left ≫
      pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
        (i₁).left =
    pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom
      (i₁).left ≫ (cylinderProjectionLift X V).left :=
    pullback.lift_fst _ _ _
  have hz₀ : (zeroNeighborhoodLift X V).left ≫
      pullback.fst ((cylinderNeighborhood X).obj V).hom (i₀).left =
    (nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left :=
    pullback.lift_fst _ _ _
  have hz₁ : (zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left ≫
      pullback.fst ((cylinderNeighborhood X₁).obj ((baseChange (π).left).obj V)).hom
        (i₁).left =
    (nativeAffineSection (.of k)
      ((toSmoothSite X₁).obj ((baseChange (π).left).obj V)) 0).left :=
    pullback.lift_fst _ _ _
  have hs : f.left ≫ pullback.snd (pullback.snd ((cylinderNeighborhood X).obj V).hom
      (p).left) (i₁).left =
    g.left ≫ pullback.snd (pullback.snd ((cylinderNeighborhood X).obj V).hom
      (p).left) (i₁).left :=
    (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  change f = g
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change (((baseChange (π).left).map (zeroNeighborhoodLift X V)).left ≫
          ((contractionZeroProjectionBaseChangeIso X).hom.app
            ((cylinderNeighborhood X).obj V)).left) ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left =
        ((zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left ≫
          ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left) ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left
      simp only [Category.assoc]
      rw [contractionZeroProjectionBaseChangeIso_fst]
      change ((baseChange (π).left).map (zeroNeighborhoodLift X V)).left ≫
          pullback.fst ((zeroNeighborhood X).obj V).hom (π).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom (i₀).left =
        (zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left ≫
          ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left ≫
          pullback.fst ((baseChange (p).left).obj ((cylinderNeighborhood X).obj V)).hom
            (i₁).left ≫ pullback.fst ((cylinderNeighborhood X).obj V).hom (p).left
      rw [← Category.assoc ((baseChange (π).left).map (zeroNeighborhoodLift X V)).left,
        hmap₀, Category.assoc, hz₀,
        ← Category.assoc ((baseChange (i₁).left).map (cylinderProjectionLift X V)).left,
        hmap₁, Category.assoc,
        ← Category.assoc (zeroNeighborhoodLift X₁ ((baseChange (π).left).obj V)).left,
        hz₁, cylinderProjectionLift_fst]
      exact congrArg (fun f ↦ f.left)
        (nativeAffineSection_naturality (.of k)
          ((restrictionProjection π).app V) 0).symm
    · change (f.left ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left) ≫
          pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left =
        (g.left ≫
          pullback.fst (pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left) (i₁).left) ≫
          pullback.snd ((cylinderNeighborhood X).obj V).hom (p).left
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs,
        Category.assoc, ← pullback.condition, ← Category.assoc]
  · exact hs

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
