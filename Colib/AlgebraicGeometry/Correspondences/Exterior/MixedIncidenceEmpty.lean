/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidence
public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence

/-!
# Nonmatching native parameter-graph components have zero incidence

A point of actual mixed incidence would belong to both the actual graph source
component and the exterior source component. Distinct components of the normal
smooth source are disjoint. Thus every nonmatching component has empty actual
incidence and zero actual Tor correspondence, without a multiplicity hypothesis.
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
  (hne : Set.range (exteriorSupportSourceProjection (SmoothSite.product X T)
    (SmoothSite.product X U)
    (nativeGraphComponent (SmoothSite.product X T) (SmoothSite.product X U)
      (SmoothSite.productMap (𝟙 X) ψ) t)) ≠
    Set.range (exteriorIdentitySource X Y T (integralComponentAt z)))

include hne

/-- No actual incidence point can lie over two distinct smooth-source components. -/
theorem nativeMixedGraphIncidence_isEmpty :
    IsEmpty (nativeMixedGraphIncidence X Y T U ψ z hz t) := by
  let : IsLocallyNoetherian ((𝟭 Scheme).obj (SmoothSite.product X T).left) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (show (SmoothSite.product X T).left ⟶ Spec (.of k) from (SmoothSite.product X T).hom)
  let : IsNormal ((𝟭 Scheme).obj (SmoothSite.product X T).left) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field
      (show (SmoothSite.product X T).left ⟶ Spec (.of k) from (SmoothSite.product X T).hom))
  have hd := disjoint_of_mem_irreducibleComponents_of_isNormal _ _
    (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
      (SmoothSite.product X U).hom (SmoothSite.productMap (𝟙 X) ψ).left
      (MorphismProperty.Over.w _) t).2
    (nativeExteriorSource_range_mem X Y T z hz) hne
  constructor
  intro w
  have hg : nativeMixedGraphSource X Y T U ψ z hz t w ∈
      Set.range (exteriorSupportSourceProjection (SmoothSite.product X T)
        (SmoothSite.product X U)
        (nativeGraphComponent (SmoothSite.product X T) (SmoothSite.product X U)
          (SmoothSite.productMap (𝟙 X) ψ) t)) :=
    ⟨(pullback.fst (C := Scheme) _ _) w, rfl⟩
  have he : nativeMixedGraphSource X Y T U ψ z hz t w ∈
      Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) :=
    ⟨nativeMixedGraphToSupport X Y T U ψ z hz t w,
      congrArg (fun f => f w) (nativeMixedGraphToSupport_source X Y T U ψ z hz t)⟩
  exact Set.disjoint_left.mp hd hg he

/-- A nonmatching actual graph component contributes zero to the native Tor cycle. -/
theorem nativeMixedGraphIncidenceTor_eq_zero :
    incidenceTorCorrespondence (SmoothSite.product X T).hom (SmoothSite.product X U).hom
      (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
      (nativeExteriorPoint X Y U z hz)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.productMap (𝟙 X) ψ).left
        (MorphismProperty.Over.w _) t)
      (nativeExteriorPoint_admissible X Y U z hz) = 0 := by
  let := nativeMixedGraphIncidence_isEmpty X Y T U ψ z hz t hne
  apply incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
  exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => isEmptyElim (⟨p, hp⟩ : genericPoints _)

attribute [colib_tag "COL-0387", colib_ref "motivic_source_a6805c4"
  "AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeIncidence.lean:292-313"
  "adaptation" "Distinct source-component images give empty incidence and zero Tor cycle"]
  nativeMixedGraphIncidence_isEmpty
  nativeMixedGraphIncidenceTor_eq_zero

end Stacks.Chow
