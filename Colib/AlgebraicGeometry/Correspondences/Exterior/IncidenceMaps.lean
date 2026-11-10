/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceIso
public import Colib.AlgebraicGeometry.Correspondences.Composition.Embedding

/-!
# Actual exterior-incidence embeddings and the finite outer map

The full product has explicit source and target maps, both retaining the same
parameter. Its two actual support inclusions give a closed immersion into the
native triple product. The native incidence isomorphism preserves that immersion
and the actual finite map used for pushforward, not just their point images.

The source and target equations adapt `motivic_source_a6805c4`,
Exterior/Identity/Incidence.lean:333-371. Finite-map compatibility and the displayed
embedding comparison are direct consequences using accepted native providers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

/-- The source projection of the full product, using its actual first support. -/
abbrev exteriorIncidenceProductSource : exteriorIncidenceProduct X Y Z T z w ⟶
    (SmoothSite.product X T).left :=
  exteriorIncidenceProductFirst X Y Z T z w ≫
    exteriorIdentitySource X Y T (integralComponentAt z)

/-- The target projection of the full product, using its actual second support. -/
abbrev exteriorIncidenceProductTarget : exteriorIncidenceProduct X Y Z T z w ⟶
    (SmoothSite.product Z T).left :=
  exteriorIncidenceProductSecond X Y Z T z w ≫
    exteriorIdentityTarget Y Z T (integralComponentAt w)

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorIncidenceProductSource_fst :
    exteriorIncidenceProductSource X Y Z T z w ≫ pullback.fst X.hom T.hom =
      pullback.fst _ _ ≫ correspondenceIncidenceLeft X.hom Y.hom Z.hom z w := by
  simp only [exteriorIncidenceProductSource, Category.assoc, exteriorIdentitySource_fst,
    exteriorIncidenceProductFirst_fst_assoc, correspondenceIncidenceLeft,
    exteriorSupportSourceProjection]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorIncidenceProductSource_snd :
    exteriorIncidenceProductSource X Y Z T z w ≫ pullback.snd X.hom T.hom =
      pullback.snd _ _ := by
  simp only [exteriorIncidenceProductSource, Category.assoc, exteriorIdentitySource_snd,
    exteriorIncidenceProductFirst_snd]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorIncidenceProductTarget_fst :
    exteriorIncidenceProductTarget X Y Z T z w ≫ pullback.fst Z.hom T.hom =
      pullback.fst _ _ ≫ correspondenceIncidenceRight X.hom Y.hom Z.hom z w := by
  simp only [exteriorIncidenceProductTarget, Category.assoc, exteriorIdentityTarget_fst,
    exteriorIncidenceProductSecond_fst_assoc, correspondenceIncidenceRight,
    exteriorSupportTargetProjection]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorIncidenceProductTarget_snd :
    exteriorIncidenceProductTarget X Y Z T z w ≫ pullback.snd Z.hom T.hom =
      pullback.snd _ _ := by
  simp only [exteriorIncidenceProductTarget, Category.assoc, exteriorIdentityTarget_snd,
    exteriorIncidenceProductSecond_snd]

/-- Compatibility with the complete native source map. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceIso_hom_source :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
      correspondenceIncidenceLeft (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom) (pullback.fst Z.hom T.hom ≫ Z.hom)
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw) =
      exteriorIncidenceProductSource X Y Z T z w := by
  exact (nativeExteriorIncidenceIso_hom_fst_assoc X Y Z T z w hz hw
    ((integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Y T).hom)).trans
    (congrArg (fun f => exteriorIncidenceProductFirst X Y Z T z w ≫ f)
      (nativeExteriorSupportIso_hom_source X Y T z hz))

/-- Compatibility with the complete native target map. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceIso_hom_target :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
      correspondenceIncidenceRight (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom) (pullback.fst Z.hom T.hom ≫ Z.hom)
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw) =
      exteriorIncidenceProductTarget X Y Z T z w := by
  exact (nativeExteriorIncidenceIso_hom_snd_assoc X Y Z T z w hz hw
    ((integralComponentAt (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
      pullback.snd (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom)).trans
    (congrArg (fun f => exteriorIncidenceProductSecond X Y Z T z w ≫ f)
      (nativeExteriorSupportIso_hom_target Y Z T w hw))

/-- The literal source-target map on the full product, before assigning any cycle. -/
def exteriorIncidenceProductMap : exteriorIncidenceProduct X Y Z T z w ⟶
    pullback (SmoothSite.product X T).hom (SmoothSite.product Z T).hom :=
  pullback.lift (exteriorIncidenceProductSource X Y Z T z w)
    (exteriorIncidenceProductTarget X Y Z T z w) (by
      simp only [SmoothSite.product_hom, ← Category.assoc,
        exteriorIncidenceProductSource_fst, exteriorIncidenceProductTarget_fst]
      simp only [Category.assoc, correspondenceIncidence_condition])

/-- The isomorphism preserves the actual finite source-target map used in composition. -/
@[reassoc]
theorem nativeExteriorIncidenceIso_hom_map :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
      correspondenceIncidenceMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
        (nativeExteriorPoint Y Z T w hw) = exteriorIncidenceProductMap X Y Z T z w := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceIncidenceMap_fst,
      exteriorIncidenceProductMap, pullback.lift_fst]
    exact nativeExteriorIncidenceIso_hom_source X Y Z T z w hz hw
  · simp only [Category.assoc, correspondenceIncidenceMap_snd,
      exteriorIncidenceProductMap, pullback.lift_snd]
    exact nativeExteriorIncidenceIso_hom_target X Y Z T z w hz hw

include hz hw in
/-- Finiteness is for the actual displayed map, not merely for its closed image. -/
theorem exteriorIncidenceProductMap_isFinite :
    IsFinite (exteriorIncidenceProductMap X Y Z T z w) := by
  let : IsFinite (correspondenceIncidenceMap (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)) :=
    isFinite_correspondenceIncidenceMap _ _ _ _ _
      (nativeExteriorPoint_admissible X Y T z hz)
      (nativeExteriorPoint_admissible Y Z T w hw)
  rw [← nativeExteriorIncidenceIso_hom_map X Y Z T z w hz hw]
  infer_instance

/-- The full product embedded by both actual exterior support closed immersions. -/
def exteriorIncidenceProductInclusion : exteriorIncidenceProduct X Y Z T z w ⟶
    correspondenceTripleProduct (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom :=
  pullback.lift
    (exteriorIncidenceProductFirst X Y Z T z w ≫
      exteriorIdentityInclusion X Y T (integralComponentAt z))
    (exteriorIncidenceProductSecond X Y Z T z w ≫
      exteriorIdentityInclusion Y Z T (integralComponentAt w)) (by
      simpa only [Category.assoc, exteriorIdentityInclusion_fst, exteriorIdentityInclusion_snd]
        using exteriorIncidenceProduct_condition X Y Z T z w)

/-- Compatibility with the native triple-product embedding retains the full closed subschemes. -/
@[reassoc]
theorem nativeExteriorIncidenceIso_hom_inclusion :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
      correspondenceIncidenceInclusion (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw) =
      exteriorIncidenceProductInclusion X Y Z T z w := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceIncidenceInclusion_fst,
      exteriorIncidenceProductInclusion, pullback.lift_fst]
    exact (nativeExteriorIncidenceIso_hom_fst_assoc X Y Z T z w hz hw
      (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι).trans
      (congrArg (fun f => exteriorIncidenceProductFirst X Y Z T z w ≫ f)
        (nativeExteriorSupportIso_hom_inclusion X Y T z hz))
  · simp only [Category.assoc, correspondenceIncidenceInclusion_snd,
      exteriorIncidenceProductInclusion, pullback.lift_snd]
    exact (nativeExteriorIncidenceIso_hom_snd_assoc X Y Z T z w hz hw
      (integralComponentAt (nativeExteriorPoint Y Z T w hw)).subschemeι).trans
      (congrArg (fun f => exteriorIncidenceProductSecond X Y Z T z w ≫ f)
        (nativeExteriorSupportIso_hom_inclusion Y Z T w hw))

include hz hw in
/-- The explicit full-product inclusion is an actual closed immersion. -/
theorem exteriorIncidenceProductInclusion_isClosedImmersion :
    IsClosedImmersion (exteriorIncidenceProductInclusion X Y Z T z w) := by
  rw [← nativeExteriorIncidenceIso_hom_inclusion X Y Z T z w hz hw]
  infer_instance

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Incidence.lean:333-371"
  "adaptation" "Exact source and target coordinates, preserving the common parameter"]
  nativeExteriorIncidenceIso_hom_source nativeExteriorIncidenceIso_hom_target

end Stacks.Chow
