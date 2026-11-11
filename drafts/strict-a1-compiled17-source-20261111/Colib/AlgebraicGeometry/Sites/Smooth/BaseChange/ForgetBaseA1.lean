/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.ForgetBase
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-!
# The actual native affine cylinder after finite separable forgetting

The native additive parameter is compared to native relative affine space.
The actual affine-space base map is Cartesian, so the forgotten L-cylinder
is the k-cylinder on the same underlying L-scheme. The comparison preserves
the literal first projection. No whole-family cycle specialization, trace
naturality or coefficient comparison is used in this geometric construction.

Adapted from motivic's `Smooth/BaseChange/ForgetBaseA1`, blob
960b55139fb235e9d61864bab8b46a551cd600d5. The original polynomial parameter is
replaced by the already active native additive parameter, via its actual
structure-map-preserving comparison with relative affine space.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The native affine parameter map induced by a genuine base map. -/
def additiveGroupBaseChangeMap {T S : Scheme.{u}} (r : T ⟶ S) :
    additiveGroupBaseChange T ⟶ additiveGroupBaseChange S :=
  (additiveGroupBaseChangeAffineSpaceIso T).hom ≫
    AffineSpace.map (ULift.{u} Unit) r ≫ (additiveGroupBaseChangeAffineSpaceIso S).inv

/-- Its structure map is the original base map, not an unspecified affine-line map. -/
@[reassoc]
theorem additiveGroupBaseChangeMap_over {T S : Scheme.{u}} (r : T ⟶ S) :
    additiveGroupBaseChangeMap r ≫ (Scheme.SmoothSite.additiveGroupObject S).hom =
      (Scheme.SmoothSite.additiveGroupObject T).hom ≫ r := by
  rw [additiveGroupBaseChangeMap,
    ← additiveGroupBaseChangeAffineSpaceIso_hom_over S]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [AffineSpace.map_over, ← Category.assoc,
    additiveGroupBaseChangeAffineSpaceIso_hom_over]

/-- Native affine parameters form the actual Cartesian square over every base map. -/
theorem additiveGroupBaseChangeMap_isPullback {T S : Scheme.{u}} (r : T ⟶ S) :
    IsPullback (Scheme.SmoothSite.additiveGroupObject T).hom
      (additiveGroupBaseChangeMap r) r (Scheme.SmoothSite.additiveGroupObject S).hom := by
  apply (AffineSpace.isPullback_map (n := ULift.{u} Unit) r).flip.of_iso'
    (additiveGroupBaseChangeAffineSpaceIso T) (Iso.refl T)
    (additiveGroupBaseChangeAffineSpaceIso S) (Iso.refl S)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      additiveGroupBaseChangeAffineSpaceIso_hom_over T
  · simp only [additiveGroupBaseChangeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      additiveGroupBaseChangeAffineSpaceIso_hom_over S

namespace Scheme.SmoothSite

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local notation "r" => finiteSeparableBaseMap k L
local notation "F" => finiteSeparableForgetBase k L

/-- The forgotten native L-cylinder is a pullback over the original k-base. -/
theorem finiteSeparableNativeCylinder_isPullback (X : SmoothSite (Spec (.of L))) :
    IsPullback (productFst X (additiveGroupObject (Spec (.of L)))).left
      (pullback.snd X.hom (additiveGroupObject (Spec (.of L))).hom ≫
        additiveGroupBaseChangeMap r)
      (X.hom ≫ r) (additiveGroupObject (Spec (.of k))).hom :=
  (IsPullback.of_hasPullback X.hom (additiveGroupObject (Spec (.of L))).hom).paste_vert
    (additiveGroupBaseChangeMap_isPullback r)

/-- The actual native cylinder isomorphism after finite separable base forgetting. -/
def finiteSeparableForgetBaseA1Iso (X : SmoothSite (Spec (.of L))) :
    F.obj (product X (additiveGroupObject (Spec (.of L)))) ≅
      product (F.obj X) (additiveGroupObject (Spec (.of k))) :=
  MorphismProperty.Over.isoMk (finiteSeparableNativeCylinder_isPullback k L X).isoPullback (by
    change (finiteSeparableNativeCylinder_isPullback k L X).isoPullback.hom ≫
        (pullback.fst (X.hom ≫ r) (additiveGroupObject (Spec (.of k))).hom ≫ (X.hom ≫ r)) =
      (pullback.fst X.hom (additiveGroupObject (Spec (.of L))).hom ≫ X.hom) ≫ r
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    simp only [productFst, homMk_left, Category.assoc])

/-- The comparison sends the literal forgotten L-projection to the literal k-projection. -/
@[reassoc]
theorem finiteSeparableForgetBaseA1Iso_hom_projection (X : SmoothSite (Spec (.of L))) :
    (finiteSeparableForgetBaseA1Iso k L X).hom ≫
        productFst (F.obj X) (additiveGroupObject (Spec (.of k))) =
      F.map (productFst X (additiveGroupObject (Spec (.of L)))) := by
  apply MorphismProperty.Over.Hom.ext
  exact (finiteSeparableNativeCylinder_isPullback k L X).isoPullback_hom_fst

end Scheme.SmoothSite

end AlgebraicGeometry
