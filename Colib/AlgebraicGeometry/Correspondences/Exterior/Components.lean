/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support

/-!
# Actual exterior source images and source-component correspondence

The source image of the literal support is the Cartesian preimage of the
original source image, and the actual image ideal retains that same image.
A geometrically integral smooth parameter supplies the native correspondence
of irreducible source components by preimage. Empty and disconnected sources
remain allowed. Adapted from motivic_source_a6805c4, Exterior/Identity/Unit.lean.
No whole graph/identity cycle equality is asserted in this geometric leaf.
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

/-- The source image of the actual support is the literal Cartesian preimage. -/
theorem exteriorIdentitySource_range :
    Set.range (exteriorIdentitySource X Y T W) =
      (pullback.fst X.hom T.hom) ⁻¹' Set.range (exteriorSupportSourceProjection X Y W) := by
  let h := exteriorIdentitySource_isPullback X Y T W
  rw [← h.isoPullback_hom_fst]
  change Set.range (fun x =>
    (pullback.fst (pullback.fst X.hom T.hom)
      (exteriorSupportSourceProjection X Y W)) (h.isoPullback.hom x)) = _
  have hh : Function.Surjective h.isoPullback.hom :=
    (Scheme.homeoOfIso h.isoPullback).surjective
  exact (hh.range_comp _).trans (Scheme.Pullback.range_fst _ _)

/-- The actual image factorization recovers the original exterior source map. -/
@[reassoc]
theorem exteriorIdentityImage_toSource :
    (exteriorIdentityInclusion X Y T W).toImage ≫
      (exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom =
      exteriorIdentitySource X Y T W := by
  change (exteriorIdentityInclusion X Y T W).toImage ≫
    (exteriorIdentityInclusion X Y T W).imageι ≫ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact exteriorIdentityInclusion_fst X Y T W

/-- Passing to the actual image ideal preserves exactly the source image. -/
theorem exteriorIdentityImage_range [IsFinite (exteriorSupportSourceProjection X Y W)] :
    Set.range ((exteriorIdentityInclusion X Y T W).ker.subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) =
      (pullback.fst X.hom T.hom) ⁻¹' Set.range (exteriorSupportSourceProjection X Y W) := by
  let e := exteriorIdentityInclusion X Y T W
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  have hr := e.toImage.surjective.range_comp
    (e.ker.subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom)
  change Set.range (e.toImage ≫ e.ker.subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) = _ at hr
  dsimp only [e] at hr
  rw [← hr, exteriorIdentityImage_toSource]
  exact exteriorIdentitySource_range X Y T W

/-- The native component correspondence for a geometrically integral smooth parameter. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Unit.lean:157-162"
  "adaptation" "Native component correspondence by actual relative-product preimage"]
def exteriorSourceComponentsEquiv [GeometricallyIntegral T.hom] :
    irreducibleComponents X.left ≃ irreducibleComponents (SmoothSite.product X T).left :=
  ((pullback.fst X.hom T.hom).irreducibleComponentsEquiv
    (pullback.fst X.hom T.hom).isOpenMap).symm

/-- No components are chosen: the component is the literal projection preimage. -/
@[simp↓]
theorem exteriorSourceComponentsEquiv_apply [GeometricallyIntegral T.hom]
    (C : irreducibleComponents X.left) :
    (exteriorSourceComponentsEquiv X T C).1 = (pullback.fst X.hom T.hom) ⁻¹' C.1 := rfl

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Unit.lean:80-101"
  "adaptation" "Source ranges of literal native supports and image ideals over an arbitrary base"]
  exteriorIdentitySource_range
  exteriorIdentityImage_range

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean:85-93"
  "specialization"
    "The inverse native component equivalence is preimage under the parameter projection"]
  exteriorSourceComponentsEquiv
  exteriorSourceComponentsEquiv_apply

end Stacks.Chow
