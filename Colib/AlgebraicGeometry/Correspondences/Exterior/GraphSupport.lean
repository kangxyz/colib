/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support

/-!
# Actual graph relations on native exterior supports

A native closed support lying in the graph of a smooth-site morphism has its
literal parameter product lying in the graph of the actual relative product
map. The same equality descends to the actual image ideal using toImage.
This adapts Exterior/Simplex/Graph.lean from motivic_source_a6805c4, without
rebuilding its old generator model. Component reindexing and the equality of
whole graph cycles are not yet asserted.
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
  (φ : X ⟶ Y)
  (hW : exteriorSupport_sourceProjection X Y W ≫ φ.left =
    exteriorSupport_targetProjection X Y W)

include hW

/-- The native support inclusion factors through the original graph. -/
theorem exteriorSupport_inclusion_eq_graph :
    W.subschemeι = exteriorSupport_sourceProjection X Y W ≫
      pullback.lift (𝟙 X.left) φ.left
        (by simp only [Category.id_comp, MorphismProperty.Over.w]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd]
    exact hW.symm

/-- On the literal support, the same parameter is retained by the product graph. -/
theorem exteriorIdentitySource_graph :
    exteriorIdentitySource X Y T W ≫ (SmoothSite.productMap φ (𝟙 T)).left =
      exteriorIdentityTarget X Y T W := by
  have hfst : (SmoothSite.productMap φ (𝟙 T)).left ≫ pullback.fst Y.hom T.hom =
      pullback.fst X.hom T.hom ≫ φ.left :=
    congrArg (fun a => a.left) (SmoothSite.productMap_fst φ (𝟙 T))
  have hsnd : (SmoothSite.productMap φ (𝟙 T)).left ≫ pullback.snd Y.hom T.hom =
      pullback.snd X.hom T.hom := by
    have h := congrArg (fun a => a.left) (SmoothSite.productMap_snd φ (𝟙 T))
    change _ = pullback.snd X.hom T.hom ≫ 𝟙 T.left at h
    exact h.trans (Category.comp_id _)
  apply pullback.hom_ext
  · simpa only [Category.assoc, hfst, exteriorIdentitySource_fst_assoc,
      exteriorIdentityTarget_fst, exteriorSupport_sourceProjection] using
      congrArg (fun a =>
        pullback.fst (exteriorSupport_sourceProjection X Y W ≫ X.hom) T.hom ≫ a) hW
  · simp only [Category.assoc, hsnd, exteriorIdentitySource_snd, exteriorIdentityTarget_snd]

/-- The native image ideal, not only its parameterized source, satisfies the graph relation. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:85-111"
  "adaptation" "Actual exterior-image ideal retains the product graph relation"]
theorem exteriorIdentityImage_graph [IsFinite (exteriorSupport_sourceProjection X Y W)] :
    (exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom ≫
          (SmoothSite.productMap φ (𝟙 T)).left =
      (exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom := by
  let e := exteriorIdentityInclusion X Y T W
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  apply (cancel_epi e.toImage).mp
  change e.toImage ≫ (e.imageι ≫ pullback.fst _ _ ≫
      (SmoothSite.productMap φ (𝟙 T)).left) =
    e.toImage ≫ (e.imageι ≫ pullback.snd _ _)
  simp only [e, ← Category.assoc, Scheme.Hom.toImage_imageι,
    exteriorIdentityInclusion_snd, exteriorIdentityInclusion_fst]
  exact exteriorIdentitySource_graph X Y T W φ hW

end Stacks.Chow
