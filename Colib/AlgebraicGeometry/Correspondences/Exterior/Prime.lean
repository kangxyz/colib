/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Dominance

/-!
# Native prime exterior correspondences

For each actual admissible native point, the literal diagonal-parameter support
maps by a closed immersion onto its actual image ideal. Its integral image is
finite over, and dominates a component of, the relative source product.
The resulting prime is Mathlib's native cycle with coefficient one at that
image's generic point. No second generator or cycle model is introduced.
Adapted from motivic_source_a6805c4, Exterior/Identity/Basic.lean.
Additive extension and composition compatibility are separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {k : Type u} [Field k]
  (X Y T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

include hz

/-- The literal image ideal has integral subscheme, not an auxiliary replacement. -/
theorem nativeExteriorImage_isIntegral :
    IsIntegral (exteriorIdentityInclusion X Y T (integralComponentAt z)).ker.subscheme := by
  let : IsFinite (exteriorSupport_sourceProjection X Y (integralComponentAt z)) := hz.1
  let := nativeExteriorSupport_isIntegral X Y T z hz
  let e := exteriorIdentityInclusion X Y T (integralComponentAt z)
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  exact IsIntegral.of_isIso e.toImage

/-- The actual prime exterior correspondence, on the native cycle object. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean:219-238"
  "adaptation" "Native prime cycle on the actual closed image of diagonal-parameter support"]
def nativeExteriorPrime :
    finiteCorrespondences (SmoothSite.product X T).hom (SmoothSite.product Y T).hom := by
  let : IsFinite (exteriorSupport_sourceProjection X Y (integralComponentAt z)) := hz.1
  let := nativeExteriorSupport_isIntegral X Y T z hz
  let e := exteriorIdentityInclusion X Y T (integralComponentAt z)
  let : IsIso e.toImage := IsClosedImmersion.instIsIsoSchemeToImage e
  let p := e.ker.subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
  have he : e.toImage ≫ p = exteriorIdentitySource X Y T (integralComponentAt z) := by
    change e.toImage ≫ (e.imageι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact exteriorIdentityInclusion_fst X Y T (integralComponentAt z)
  have hf : IsFinite p := by
    have : IsFinite (e.toImage ≫ p) := by
      rw [he]
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.toImage p).mp this
  have hc : Set.range p ∈ irreducibleComponents (SmoothSite.product X T).left := by
    have hr : Set.range (e.toImage ≫ p) = Set.range p := e.toImage.surjective.range_comp p
    rw [← hr, he]
    exact nativeExteriorSource_range_mem X Y T z hz
  exact finiteCorrespondenceOfIntegralClosedSubscheme
    (SmoothSite.product X T).hom (SmoothSite.product Y T).hom e.ker
    (nativeExteriorImage_isIntegral X Y T z hz) hf hc

/-- The actual image generic point has literal coefficient one. -/
theorem nativeExteriorPrime_apply :
    (nativeExteriorPrime X Y T z hz).1
      (genericPointOf (exteriorIdentityInclusion X Y T (integralComponentAt z)).ker
        (nativeExteriorImage_isIntegral X Y T z hz)) = 1 := by
  classical
  simp [nativeExteriorPrime, finiteCorrespondenceOfIntegralClosedSubscheme]

end Stacks.Chow
