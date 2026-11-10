/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceIso

/-!
# The mixed-incidence isomorphism preserves the actual finite map

The actual source-target incidence map becomes the existing native graph
postcomposition map on the actual exterior prime support. Both coordinates
are retained, not merely the image set. This is the finite-map comparison
needed before transporting any Tor cycle; no Tor transversality is assumed.
Adapted from motivic_source_a6805c4, Exterior/Simplex/GraphInterchangeIncidence.lean.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow
variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (hRange : Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
    Set.range (nativeParameterGraphSource X T U ψ t))

/-- Equality of the actual finite maps under the actual support isomorphism. -/
theorem nativeMixedGraphIncidenceIso_hom_map :
    (nativeMixedGraphIncidenceIso X Y T U ψ z hz t hRange).hom ≫
      correspondenceIncidenceMap (SmoothSite.product X T).hom (SmoothSite.product X U).hom
        (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
        (nativeExteriorPoint X Y U z hz) =
    (nativeExteriorSupportIso X Y T z hz).hom ≫
      correspondenceGraphPostcompositionMap (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Y U).hom
        (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
        (nativeExteriorPoint X Y T z hz) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceIncidenceMap_fst,
      correspondenceGraphPostcompositionMap_fst]
    change nativeSupportToMixedGraph X Y T U ψ z hz t hRange ≫
      nativeMixedGraphSource X Y T U ψ z hz t = _
    rw [nativeSupportToMixedGraph_source, nativeExteriorSupportIso_hom_source]
  · simp only [Category.assoc, correspondenceIncidenceMap_snd,
      correspondenceGraphPostcompositionMap_snd]
    change nativeSupportToMixedGraph X Y T U ψ z hz t hRange ≫
      pullback.snd _ _ ≫ (integralComponentAt (nativeExteriorPoint X Y U z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X U).hom (SmoothSite.product Y U).hom = _
    rw [nativeSupportToMixedGraph_snd_assoc]
    simp only [nativeExteriorSupportIso_hom_target,
      nativeExteriorSupportIso_hom_target_assoc]
    exact exteriorParameterMap_target X Y (integralComponentAt z) ψ

attribute [colib_tag "COL-0387", colib_ref "motivic_source_a6805c4"
  "AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeIncidence.lean:319-334"
  "adaptation" "Native cycle support, maps and explicitly stated hypotheses"]
  nativeMixedGraphIncidenceIso_hom_map

end Stacks.Chow
