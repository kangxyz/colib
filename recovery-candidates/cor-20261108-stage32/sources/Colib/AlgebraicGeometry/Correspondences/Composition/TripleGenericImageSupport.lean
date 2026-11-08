/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImage
public import Colib.AlgebraicGeometry.Correspondences.Composition.ComponentDominance

/-!
# Actual triple generic support on the whole image

Finite correspondence support projections over smooth schemes are universally open by
native Stacks 0F32. Their base changes and composites send actual generic points to source
component generic points. The finite whole-image source map reflects those generic points,
since its fibres are discrete. Thus actual triple generics map to generic points of the
whole image incidence.
This lower leaf imports only existing geometry, without the Tor family or Euler joins.

No openness, flatness, reduction, normality, or component hypothesis is imposed on the whole
image or the triple-to-image map. Normality is used only for the original smooth factors,
component by component. The argument works over arbitrary fields and disconnected schemes.

References: Stacks 0F32 (quasi-finite component dominance implies universal openness),
040F (open morphisms lift generalizations), 02R4 (finite pushforward support), and
Mazza--Voevodsky--Weibel, Lemma 1.7, printed page 5. Implementation comparison:
independent motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean, lines 205-245.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- A point above a generic point under a finite morphism is generic. The actual fibre,
not a reduced or integral replacement, has no nontrivial specializations. -/
theorem mem_genericPoints_of_finite_image {A B : Scheme.{u}} (p : A ⟶ B) [IsFinite p]
    (a : A) (ha : p a ∈ genericPoints B) : a ∈ genericPoints A := by
  apply (mem_genericPoints_iff_forall_specializes_eq a).mpr
  intro a' ha'
  have he : p a' = p a :=
    (mem_genericPoints_iff_forall_specializes_eq (p a)).mp ha _ (ha'.map p.continuous)
  let : DiscreteTopology (p ⁻¹' {p a}) :=
    isDiscrete_iff_discreteTopology.mp (p.isDiscrete_preimage_singleton (p a))
  let b : p ⁻¹' {p a} := ⟨a', he⟩
  let c : p ⁻¹' {p a} := ⟨a, rfl⟩
  have hbc : b ⤳ c := (subtype_specializes_iff ..).mpr ha'
  exact congrArg Subtype.val hbc.eq

variable {K : Type u} [Field K]

/-- The actual finite integral support projection is universally open over the original
smooth source. Its image is its given source component, not the whole disconnected source. -/
theorem universallyOpen_finiteCorrespondenceProjection_of_smooth
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [Smooth f]
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    UniversallyOpen ((integralComponentAt z).subschemeι ≫ pullback.fst f g) := by
  let a := (integralComponentAt z).subschemeι ≫ pullback.fst f g
  let : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsFinite a := hz.1
  apply universallyOpen_of_locallyQuasiFinite_of_dominant_components a
    isGeometricallyUnibranch_of_isNormal
  intro C
  have hC : (C : Set (integralComponentAt z).subscheme) = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.2
  refine ⟨⟨Set.range a, hz.2⟩, ?_⟩
  rw [hC, Set.image_univ]
  exact a.isClosedMap.isClosed_range.closure_eq

/-- Every generic point of the actual pair incidence maps to a source component generic. -/
theorem mem_genericPoints_correspondenceIncidenceLeft_of_smooth
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (h : Z ⟶ Spec (.of K)) [Smooth f] [Smooth g]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    correspondenceIncidenceLeft f g h z w t ∈ genericPoints X := by
  let := universallyOpen_finiteCorrespondenceProjection_of_smooth f g z hz
  let := universallyOpen_finiteCorrespondenceProjection_of_smooth g h w hw
  let : UniversallyOpen (correspondenceIncidenceLeft f g h z w) := by
    dsimp only [correspondenceIncidenceLeft]
    infer_instance
  exact mem_genericPoints_of_generalizingMap
    ((liftsGeneralizations_iff_generalizingMap _).mp
      (liftsGeneralizations_of_isOpenMap _
        (correspondenceIncidenceLeft f g h z w).isOpenMap)) ht

variable {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual triple projection sends generics to original pair generics by base change
of the universally open third-support projection. -/
theorem mem_genericPoints_correspondenceTripleIncidenceFst_of_smooth [Smooth h]
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : correspondenceTripleIncidence f g h i z w v)
    (ht : t ∈ genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    correspondenceTripleIncidenceFst f g h i z w v t ∈
      genericPoints (correspondenceIncidence f g h z w) := by
  let := universallyOpen_finiteCorrespondenceProjection_of_smooth h i v hv
  let : UniversallyOpen (correspondenceTripleIncidenceFst f g h i z w v) := by
    dsimp only [correspondenceTripleIncidenceFst]
    infer_instance
  exact mem_genericPoints_of_generalizingMap
    ((liftsGeneralizations_iff_generalizingMap _).mp
      (liftsGeneralizations_of_isOpenMap _
        (correspondenceTripleIncidenceFst f g h i z w v).isOpenMap)) ht

/-- The actual common triple has finitely many generic points, without quasi-compactness
of any ambient smooth factor. Its generics lie over the finite original pair generic set. -/
theorem finite_genericPoints_correspondenceTripleIncidence_of_smooth [Smooth g] [Smooth h]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    (genericPoints (correspondenceTripleIncidence f g h i z w v)).Finite := by
  let := isFinite_correspondenceTripleIncidenceFst f g h i z w v hv
  let : IsNormal Y := isNormal_of_isRegular Y (isRegular_of_smooth_over_field g)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  refine ((correspondenceTripleIncidenceFst f g h i z w v).finite_preimage
    (finite_genericPoints_correspondenceIncidence f g h z w hw)).subset ?_
  intro t ht
  exact mem_genericPoints_correspondenceTripleIncidenceFst_of_smooth f g h i z w v hv t ht

/-- The genuine triple-to-image map sends every original triple generic to a whole-image
incidence generic. Only the whole-image source map is used for generic reflection. -/
theorem mem_genericPoints_correspondenceTripleToLeftImageIncidence
    [Smooth f] [Smooth g] [Smooth h] [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : correspondenceTripleIncidence f g h i z w v)
    (ht : t ∈ genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    correspondenceTripleToLeftImageIncidence f g h i z w v t ∈
      genericPoints (correspondenceLeftImageIncidence f g h i z w v) := by
  let C := correspondenceIntermediateImageTarget f g h z w
  let B := (integralComponentAt v).subschemeι ≫ pullback.fst h i
  let r := correspondenceIncidenceMap f g h z w
  let p := pullback.fst C B ≫ (r.imageι ≫ pullback.fst f h)
  let := hv.1
  let := isFinite_correspondenceIntermediateImageSource f g h z w hz hw
  let : IsFinite p := by dsimp only [p, B, r]; infer_instance
  apply mem_genericPoints_of_finite_image p
  have hsource : correspondenceTripleToLeftImageIncidence f g h i z w v ≫ p =
      correspondenceTripleIncidenceSource f g h i z w v := by
    simp [p, C, B, r, correspondenceTripleToLeftImageIncidence,
      correspondenceTripleIncidenceSource, correspondenceTripleIncidenceFst,
      correspondenceIncidenceLeft, correspondenceIncidenceMap_fst, pullback.map,
      Category.assoc]
  rw [← Scheme.Hom.comp_apply, hsource]
  exact mem_genericPoints_correspondenceIncidenceLeft_of_smooth f g h z w hz hw _
    (mem_genericPoints_correspondenceTripleIncidenceFst_of_smooth f g h i z w v hv t ht)

end Stacks.Chow
