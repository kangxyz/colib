/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Sheaf
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Cokernel

/-! # The canonical original-contraction map to the actual boundary sheaf -/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/Contraction/Basic.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `2ef3aff4b7e4397444db5fc98deae20c55a76214`.
The actual native additive and multiplicative parameter objects and the existing
small-site image adjunction are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : PresheafWithTransfers.{u + 1} k)

/-- The actual boundary sheaf of the zero section in the literal affine-line cylinder. -/
abbrev zeroSectionBoundary := presheafBoundary ((PresheafWithTransfers.toPresheaf k).obj F)
  (SmoothSite.Contraction.openInclusion.app X) (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)

/-- Laurent sections map to the actual ambient sheaf cokernel on cylinder neighborhoods. -/
def laurentToAmbientCokernel :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections F) ⟶
    (cylinderNeighborhood X).op ⋙
      (presheafBoundaryAmbient ((PresheafWithTransfers.toPresheaf k).obj F)
        (SmoothSite.Contraction.openInclusion.app X)).obj :=
  Functor.whiskerLeft (toSmoothSite X).op
      (PresheafWithTransfers.withParameterUnderlyingIso F (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom ≫
    Functor.whiskerRight (NatTrans.op (puncturedProjectionNat X))
      ((PresheafWithTransfers.toPresheaf k).obj F) ≫
    Functor.whiskerLeft (cylinderNeighborhood X).op
      (presheafBoundaryProjection ((PresheafWithTransfers.toPresheaf k).obj F)
        (SmoothSite.Contraction.openInclusion.app X))

/-- From the ambient cokernel on cylinder neighborhoods to its true closed inverse image. -/
def ambientCokernelToBoundary :
    (cylinderNeighborhood X).op ⋙
      (presheafBoundaryAmbient ((PresheafWithTransfers.toPresheaf k).obj F)
        (SmoothSite.Contraction.openInclusion.app X)).obj ⟶ (zeroSectionBoundary X F).obj :=
  Functor.whiskerLeft (cylinderNeighborhood X).op
      ((imageAdjunction (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).unit.app
        (presheafBoundaryAmbient ((PresheafWithTransfers.toPresheaf k).obj F)
          (SmoothSite.Contraction.openInclusion.app X))).hom ≫
    Functor.whiskerRight (NatTrans.op (zeroNeighborhoodLiftNat X))
      (zeroSectionBoundary X F).obj

/-- The original affine-line-to-Laurent restriction, restricted to the small site. -/
abbrev contractionRestrictionSmall :=
  Functor.whiskerLeft (toSmoothSite X).op
    ((PresheafWithTransfers.toPresheaf k).map
      (PresheafWithTransfers.contractionRestriction F))

/-- The ambient boundary kills exactly the original affine-line restriction. -/
theorem restriction_laurentToAmbientCokernel :
    contractionRestrictionSmall X F ≫ laurentToAmbientCokernel X F = 0 := by
  apply NatTrans.ext
  funext V
  let G := ((PresheafWithTransfers.toPresheaf k).obj F)
  change G.map (SmoothSite.Contraction.openInclusion.app ((toSmoothSite X).obj V.unop)).op ≫
    (𝟙 _ ≫ G.map (puncturedProjection X V.unop).op ≫
      (presheafBoundaryProjection G (SmoothSite.Contraction.openInclusion.app X)).app
        (op ((cylinderNeighborhood X).obj V.unop))) = 0
  rw [Category.id_comp, ← Category.assoc, ← G.map_comp, ← op_comp,
    puncturedProjection_open, op_comp, G.map_comp, Category.assoc]
  have h := congr_app (presheafBoundaryRestriction_projection G
    (SmoothSite.Contraction.openInclusion.app X)) (op ((cylinderNeighborhood X).obj V.unop))
  change G.map ((restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app
      ((cylinderNeighborhood X).obj V.unop)).op ≫
      (presheafBoundaryProjection G (SmoothSite.Contraction.openInclusion.app X)).app
        (op ((cylinderNeighborhood X).obj V.unop)) = 0 at h
  rw [h, comp_zero]

/-- Restriction preserves the original presheaf contraction cokernel literally. -/
def contractionRestrictedCokernelIso :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction F) ≅
      cokernel (contractionRestrictionSmall X F) :=
  PreservesCokernel.iso
    (PresheafWithTransfers.forget ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (toSmoothSite X ⋙ Cor.graphFunctor k).op)
    (PresheafWithTransfers.contractionRestriction F)

/-- The canonical map from the unchanged original contraction to the boundary sheaf. -/
def contractionToBoundaryPresheaf :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction F) ⟶ (zeroSectionBoundary X F).obj :=
  (contractionRestrictedCokernelIso X F).hom ≫
    cokernel.desc _ (laurentToAmbientCokernel X F)
      (restriction_laurentToAmbientCokernel X F) ≫
    ambientCokernelToBoundary X F

/-- Sheafify the unchanged original contraction, without sheafifying the coefficient first. -/
def contractionToBoundary :
    (presheafToSheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}).obj
      ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
        (PresheafWithTransfers.contraction F)) ⟶ zeroSectionBoundary X F where
  hom := sheafifyLift (nisnevichTopology X.left) (contractionToBoundaryPresheaf X F)
    (zeroSectionBoundary X F).property

@[reassoc (attr := simp)]
theorem toSheafify_contractionToBoundary :
    toSheafify (nisnevichTopology X.left) _ ≫ (contractionToBoundary X F).hom =
      contractionToBoundaryPresheaf X F :=
  toSheafify_sheafifyLift _ _ _

/-- The comparison on the original Laurent representative is the actual sheaf
cokernel projection followed by the closed inverse-image unit and zero lift. -/
@[reassoc (attr := simp)]
theorem toContraction_contractionToBoundaryPresheaf :
    Functor.whiskerLeft (toSmoothSite X).op
        ((PresheafWithTransfers.toPresheaf k).map (PresheafWithTransfers.toContraction F)) ≫
      contractionToBoundaryPresheaf X F =
      laurentToAmbientCokernel X F ≫ ambientCokernelToBoundary X F := by
  have h := PreservesCokernel.π_iso_hom
    (PresheafWithTransfers.forget ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (toSmoothSite X ⋙ Cor.graphFunctor k).op)
    (PresheafWithTransfers.contractionRestriction F)
  change Functor.whiskerLeft (toSmoothSite X).op
      ((PresheafWithTransfers.toPresheaf k).map (PresheafWithTransfers.toContraction F)) ≫
      (contractionRestrictedCokernelIso X F).hom =
      cokernel.π (contractionRestrictionSmall X F) at h
  simp only [contractionToBoundaryPresheaf, ← Category.assoc, h, cokernel.π_desc]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

