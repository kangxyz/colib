/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericImageSupport

/-!
# Component dominance of native exterior supports

For an actual admissible native correspondence point over a field, the literal
support product with a geometrically integral smooth parameter is integral,
and its finite source projection has image an actual source component.
Reuse the established native Stacks universal-openness theorem; do not add an
openness provider or assume the smooth schemes globally integral.
Adapted from motivic_source_a6805c4, Exterior/Identity/Basic.lean.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {k : Type u} [Field k]
  (X Y T : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) X.hom Y.hom) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

include hz

theorem nativeExteriorSupport_isIntegral [GeometricallyIntegral T.hom] :
    IsIntegral (exteriorIdentitySupport X Y T (integralComponentAt z)) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian
    (show X.left ⟶ Spec (.of k) from X.hom)
  let : IsLocallyNoetherian (integralComponentAt z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (exteriorSupportSourceProjection X Y (integralComponentAt z))
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  infer_instance

/-- Universal openness is proved from actual admissibility and smoothness. -/
theorem nativeExteriorSource_universallyOpen :
    UniversallyOpen (exteriorIdentitySource X Y T (integralComponentAt z)) := by
  let : UniversallyOpen (exteriorSupportSourceProjection X Y (integralComponentAt z)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth X.hom Y.hom z hz
  exact MorphismProperty.of_isPullback
    (exteriorIdentitySource_isPullback X Y T (integralComponentAt z)).flip inferInstance

/-- The actual finite exterior support dominates a component, including disconnected sources. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean:180-192"
  "adaptation" "Native support projection dominates an actual relative-source component"]
theorem nativeExteriorSource_range_mem [GeometricallyIntegral T.hom] :
    Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ∈
      irreducibleComponents (SmoothSite.product X T).left := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let := nativeExteriorSupport_isIntegral X Y T z hz
  let := nativeExteriorSource_universallyOpen X Y T z hz
  let p := exteriorIdentitySource X Y T (integralComponentAt z)
  have hg := mem_genericPoints_of_generalizingMap
    ((liftsGeneralizations_iff_generalizingMap p).mp
      (liftsGeneralizations_of_isOpenMap p p.isOpenMap))
    (by simp [genericPoints_eq_singleton] :
      genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z)) ∈
        genericPoints (exteriorIdentitySupport X Y T (integralComponentAt z)))
  change closure ({p (genericPoint (exteriorIdentitySupport X Y T (integralComponentAt z)))} :
    Set (SmoothSite.product X T).left) ∈ irreducibleComponents _ at hg
  rw [← Set.image_singleton, p.isClosedMap.closure_image_eq_of_continuous p.continuous,
    (genericPoint_spec (exteriorIdentitySupport X Y T (integralComponentAt z))).def,
    Set.image_univ] at hg
  exact hg

end Stacks.Chow
