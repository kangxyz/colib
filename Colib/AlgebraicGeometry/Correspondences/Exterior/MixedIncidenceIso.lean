/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidence
public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence

/-!
# Actual mixed incidence for a compatible graph component

When the actual graph component contains the exterior source image, the actual
native incidence is isomorphic to the literal exterior support. The graph source
projection is the existing native open immersion on a normal smooth scheme.
The range hypothesis selects the compatible component; it supplies no graph
identity, scheme isomorphism or Tor equality.

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
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

/-- Source projection of the actual integral component of the parameter graph. -/
abbrev nativeParameterGraphSource :=
  (integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product X U).hom

instance nativeParameterGraphSource_isOpenImmersion :
    IsOpenImmersion (nativeParameterGraphSource X T U ψ t) := by
  let : IsLocallyNoetherian ((𝟭 Scheme).obj (SmoothSite.product X T).left) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (show (SmoothSite.product X T).left ⟶ Spec (.of k) from (SmoothSite.product X T).hom)
  let : IsNormal ((𝟭 Scheme).obj (SmoothSite.product X T).left) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field
      (show (SmoothSite.product X T).left ⟶ Spec (.of k) from (SmoothSite.product X T).hom))
  exact isOpenImmersion_integralComponentAt_graphMap_fst (SmoothSite.product X T).hom
    (SmoothSite.product X U).hom (SmoothSite.productMap (𝟙 X) ψ).left
    (MorphismProperty.Over.w _) t

variable (hRange : Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
  Set.range (nativeParameterGraphSource X T U ψ t))

/-- The actual exterior source lifts into the compatible open graph component. -/
def nativeExteriorToGraphSupport : exteriorIdentitySupport X Y T (integralComponentAt z) ⟶
    (integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subscheme :=
  IsOpenImmersion.lift (nativeParameterGraphSource X T U ψ t)
    (exteriorIdentitySource X Y T (integralComponentAt z)) hRange

omit [GeometricallyIntegral U.hom] in
@[reassoc]
theorem nativeExteriorToGraphSupport_source :
    nativeExteriorToGraphSupport X Y T U ψ z t hRange ≫
      nativeParameterGraphSource X T U ψ t =
    exteriorIdentitySource X Y T (integralComponentAt z) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The genuine support map into the actual native mixed incidence. -/
def nativeSupportToMixedGraph : exteriorIdentitySupport X Y T (integralComponentAt z) ⟶
    nativeMixedGraphIncidence X Y T U ψ z hz t :=
  pullback.lift (nativeExteriorToGraphSupport X Y T U ψ z t hRange)
    (exteriorParameterMap X Y (integralComponentAt z) ψ ≫
      (nativeExteriorSupportIso X Y U z hz).hom) (by
      have hg := nativeGraphComponent_projection_graph (SmoothSite.product X T)
        (SmoothSite.product X U) (SmoothSite.productMap (𝟙 X) ψ) t
      change nativeParameterGraphSource X T U ψ t ≫
        (SmoothSite.productMap (𝟙 X) ψ).left =
          (integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subschemeι ≫
            pullback.snd (SmoothSite.product X T).hom (SmoothSite.product X U).hom at hg
      rw [← hg, ← Category.assoc, nativeExteriorToGraphSupport_source]
      rw [Category.assoc, nativeExteriorSupportIso_hom_source]
      exact (exteriorParameterMap_source X Y (integralComponentAt z) ψ).symm)

@[reassoc]
theorem nativeSupportToMixedGraph_fst :
    nativeSupportToMixedGraph X Y T U ψ z hz t hRange ≫ pullback.fst _ _ =
      nativeExteriorToGraphSupport X Y T U ψ z t hRange :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem nativeSupportToMixedGraph_snd :
    nativeSupportToMixedGraph X Y T U ψ z hz t hRange ≫ pullback.snd _ _ =
      exteriorParameterMap X Y (integralComponentAt z) ψ ≫
        (nativeExteriorSupportIso X Y U z hz).hom :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem nativeSupportToMixedGraph_source :
    nativeSupportToMixedGraph X Y T U ψ z hz t hRange ≫
      nativeMixedGraphSource X Y T U ψ z hz t =
    exteriorIdentitySource X Y T (integralComponentAt z) := by
  change nativeSupportToMixedGraph X Y T U ψ z hz t hRange ≫
    (pullback.fst _ _ ≫ nativeParameterGraphSource X T U ψ t) = _
  rw [← Category.assoc, nativeSupportToMixedGraph_fst, nativeExteriorToGraphSupport_source]

/-- Literal exterior support equals the actual incidence on the compatible component. -/
def nativeMixedGraphIncidenceIso : exteriorIdentitySupport X Y T (integralComponentAt z) ≅
    nativeMixedGraphIncidence X Y T U ψ z hz t where
  hom := nativeSupportToMixedGraph X Y T U ψ z hz t hRange
  inv := nativeMixedGraphToSupport X Y T U ψ z hz t
  hom_inv_id := by
    apply (exteriorParameterMap_source_isPullback X Y (integralComponentAt z) ψ).hom_ext
    · simp only [Category.assoc, nativeMixedGraphToSupport_parameter,
        nativeMixedGraphToChangedSupport, nativeSupportToMixedGraph_snd_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, nativeMixedGraphToSupport_source,
        nativeSupportToMixedGraph_source, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (nativeParameterGraphSource X T U ψ t)).mp
      simp only [Category.assoc, nativeSupportToMixedGraph_fst,
        nativeExteriorToGraphSupport_source, nativeMixedGraphToSupport_source,
        nativeMixedGraphSource, correspondenceIncidenceLeft,
        nativeParameterGraphSource, Category.id_comp]
    · simp only [Category.assoc, nativeSupportToMixedGraph_snd,
        nativeMixedGraphToSupport_parameter_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]

attribute [colib_tag "COL-0387", colib_ref "motivic_source_a6805c4"
  "AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeIncidence.lean:211-238"
  "adaptation" "Native cycle support, maps and explicitly stated hypotheses"]
  nativeMixedGraphIncidenceIso

end Stacks.Chow
