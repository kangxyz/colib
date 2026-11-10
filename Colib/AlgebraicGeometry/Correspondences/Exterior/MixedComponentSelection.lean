/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceEmpty
public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceIso

/-!
# The unique actual graph component matching an exterior support

The actual finite exterior source range is an irreducible component when the
parameter is geometrically integral. Its native generic point selects exactly
one component of the actual parameter graph: graph-component source ranges
are precisely the closures of the corresponding source generic points.

This supplies the compatible-component range condition from geometry rather
than assuming it. All other graph components have empty actual incidence and
zero actual Tor correspondence by the existing disjoint-component theorem.
There are no chosen multipliers, replacement supports or assumed graph equations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

/-- The native generic of the actual exterior source component. -/
@[colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Topology/Sober.lean:303-314"
  "ingredient" "Native generic point of the actual exterior source irreducible component"]
def nativeMixedMatchingComponent : genericPoints (SmoothSite.product X T).left :=
  genericPoints.ofComponent ⟨Set.range (exteriorIdentitySource X Y T (integralComponentAt z)),
    nativeExteriorSource_range_mem X Y T z hz⟩

/-- The selected generic has exactly the actual exterior source range as its closure. -/
theorem nativeMixedMatchingComponent_closure :
    closure ({(nativeMixedMatchingComponent X Y T z hz).val} :
      Set (SmoothSite.product X T).left) =
      Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) :=
  congrArg Subtype.val (genericPoints.component_ofComponent
    ⟨Set.range (exteriorIdentitySource X Y T (integralComponentAt z)),
      nativeExteriorSource_range_mem X Y T z hz⟩)

variable (U : SmoothSite (Spec (.of k))) (ψ : T ⟶ U)

/-- The literal source range of the selected actual graph component matches the exterior support. -/
theorem nativeMixedMatchingComponent_source_range :
    Set.range (nativeParameterGraphSource X T U ψ (nativeMixedMatchingComponent X Y T z hz)) =
      Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) := by
  change Set.range (exteriorSupportSourceProjection (SmoothSite.product X T)
    (SmoothSite.product X U) (nativeGraphComponent (SmoothSite.product X T)
      (SmoothSite.product X U) (SmoothSite.productMap (𝟙 X) ψ)
      (nativeMixedMatchingComponent X Y T z hz))) = _
  rw [nativeGraphComponent_source_range]
  exact nativeMixedMatchingComponent_closure X Y T z hz

/-- Equality of actual source ranges characterizes the unique matching graph component. -/
@[colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Topology/Sober.lean:293-299"
  "ingredient" "Injectivity of native generic-point components gives uniqueness of the \
    matching actual graph source"]
theorem nativeParameterGraphSource_range_eq_iff
    (t : genericPoints (SmoothSite.product X T).left) :
    Set.range (nativeParameterGraphSource X T U ψ t) =
        Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ↔
      t = nativeMixedMatchingComponent X Y T z hz := by
  constructor
  · intro ht
    apply genericPoints.component_injective
    apply Subtype.ext
    change closure ({t.val} : Set (SmoothSite.product X T).left) =
      closure ({(nativeMixedMatchingComponent X Y T z hz).val} :
        Set (SmoothSite.product X T).left)
    rw [nativeMixedMatchingComponent_closure]
    change Set.range (exteriorSupportSourceProjection (SmoothSite.product X T)
      (SmoothSite.product X U) (nativeGraphComponent (SmoothSite.product X T)
        (SmoothSite.product X U) (SmoothSite.productMap (𝟙 X) ψ) t)) = _ at ht
    rwa [nativeGraphComponent_source_range] at ht
  · rintro rfl
    exact nativeMixedMatchingComponent_source_range X Y T z hz U ψ

/-- The precise range hypothesis needed by the actual matched-incidence isomorphism. -/
theorem nativeMixedMatchingComponent_range_subset :
    Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
      Set.range (nativeParameterGraphSource X T U ψ (nativeMixedMatchingComponent X Y T z hz)) :=
  (nativeMixedMatchingComponent_source_range X Y T z hz U ψ).symm.subset

include hz in
/-- Existence and uniqueness use the literal source range, not an abstract graph-support label. -/
theorem existsUnique_nativeParameterGraphComponent_matching :
    ∃! t : genericPoints (SmoothSite.product X T).left,
      Set.range (nativeParameterGraphSource X T U ψ t) =
        Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) :=
  ⟨nativeMixedMatchingComponent X Y T z hz,
    nativeMixedMatchingComponent_source_range X Y T z hz U ψ,
    fun t ht => (nativeParameterGraphSource_range_eq_iff X Y T z hz U ψ t).mp ht⟩

variable [GeometricallyIntegral U.hom]

/-- The selected component gives an actual support-to-incidence isomorphism
with no range provider. -/
def nativeMixedMatchingComponentIncidenceIso :
    exteriorIdentitySupport X Y T (integralComponentAt z) ≅
      nativeMixedGraphIncidence X Y T U ψ z hz (nativeMixedMatchingComponent X Y T z hz) :=
  nativeMixedGraphIncidenceIso X Y T U ψ z hz (nativeMixedMatchingComponent X Y T z hz)
    (nativeMixedMatchingComponent_range_subset X Y T z hz U ψ)

/-- Every other actual parameter-graph component has empty actual incidence. -/
theorem nativeMixedGraphIncidence_isEmpty_of_ne_matching
    (t : genericPoints (SmoothSite.product X T).left)
    (ht : t ≠ nativeMixedMatchingComponent X Y T z hz) :
    IsEmpty (nativeMixedGraphIncidence X Y T U ψ z hz t) := by
  apply nativeMixedGraphIncidence_isEmpty X Y T U ψ z hz t
  change Set.range (nativeParameterGraphSource X T U ψ t) ≠ _
  exact fun he => ht ((nativeParameterGraphSource_range_eq_iff X Y T z hz U ψ t).mp he)

/-- Every other component contributes zero to the original native Tor correspondence. -/
theorem nativeMixedGraphIncidenceTor_eq_zero_of_ne_matching
    (t : genericPoints (SmoothSite.product X T).left)
    (ht : t ≠ nativeMixedMatchingComponent X Y T z hz) :
    incidenceTorCorrespondence (SmoothSite.product X T).hom (SmoothSite.product X U).hom
      (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
      (nativeExteriorPoint X Y U z hz)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.productMap (𝟙 X) ψ).left
        (MorphismProperty.Over.w _) t)
      (nativeExteriorPoint_admissible X Y U z hz) = 0 := by
  apply nativeMixedGraphIncidenceTor_eq_zero X Y T U ψ z hz t
  change Set.range (nativeParameterGraphSource X T U ψ t) ≠ _
  exact fun he => ht ((nativeParameterGraphSource_range_eq_iff X Y T z hz U ψ t).mp he)

end Stacks.Chow
