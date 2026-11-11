/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineOpenFiberTor
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatFiber
public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence
public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledStalkModules
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingProjection
public import Colib.AlgebraicGeometry.Correspondences.Composition.GlobalActualTorComparison

/-!
# The actual left graph projection and an affine-line endpoint

The full pulled graph component is open over the outer product: this is the
base change of the genuine graph component's source projection. Its projection
to the right adjacent product is that open map followed by the original graph
base-change map. No support is replaced by a reduced inverse image.

When the original graph map is a Cartesian affine-line endpoint, the outer
product is the entire endpoint of the right adjacent product. The native
flat-projection Tor comparison and the literal regular endpoint cut then kill
positive pulled-support Tor for an A1-flat right support. The source can be
empty or disconnected. No component-flatness over the middle source is used.

The endpoint Cartesian square is geometric input, not a cycle equation. The
literal polynomial sections are instantiated in the following module.
Implementation provenance: a new native proof toward motivic
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Graph/Flat/LeftComposition.lean`.
This is not a byte restoration of that source. It does not infer component
flatness over the full source from whole-family flatness. Native geometric and Tor suppliers
are identified by the precise direct imports and SOURCE_REVIEW.md.

-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The full left pulled support keeps its actual two outer coordinates. -/
def correspondenceLeftPulledOuter (z : pullback (C := Scheme) f g) :
    (correspondenceLeftPulledIdeal f g h z).subscheme ⟶ pullback f h :=
  correspondenceLeftPulledInclusion f g h z ≫ correspondenceTripleOuterProjection f g h

/-- This projection is the actual base change of the original source projection. -/
theorem isPullback_correspondenceLeftPulledOuter (z : pullback (C := Scheme) f g) :
    IsPullback (correspondenceLeftPulledOuter f g h z)
      (correspondenceLeftPulledProjection f g h z) (pullback.fst f h)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g) :=
  (isPullback_correspondenceLeftPulled f g h z).paste_horiz
    (correspondenceTripleOuterProjection_isPullback f g h)

@[reassoc (attr := simp)] theorem correspondenceLeftPulledOuter_fst
    (z : pullback (C := Scheme) f g) :
    correspondenceLeftPulledOuter f g h z ≫ pullback.fst f h =
      correspondenceLeftPulledProjection f g h z ≫
        (integralComponentAt z).subschemeι ≫ pullback.fst f g :=
  (isPullback_correspondenceLeftPulledOuter f g h z).w

variable (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]

/-- Every actual pulled graph component is open over the outer product. -/
theorem isOpenImmersion_correspondenceLeftPulledOuter_graphMap
    [IsLocallyNoetherian X] [IsNormal X] (s : genericPoints X) :
    IsOpenImmersion (correspondenceLeftPulledOuter f g h
      (correspondenceGraphMap f g φ hφ s.val)) := by
  haveI := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ s
  exact MorphismProperty.of_isPullback
    (isPullback_correspondenceLeftPulledOuter f g h
      (correspondenceGraphMap f g φ hφ s.val)).flip inferInstance

/-- The actual right projection factors through the genuine graph ambient map. -/
theorem correspondenceLeftPulledOuter_graphMap_right (s : X) :
    correspondenceLeftPulledInclusion f g h (correspondenceGraphMap f g φ hφ s) ≫
      pullback.snd (pullback.snd f g) (pullback.fst g h) =
    correspondenceLeftPulledOuter f g h (correspondenceGraphMap f g φ hφ s) ≫
      correspondenceGraphFiberAmbientMap f g h φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
      pullback.lift_fst, correspondenceLeftPulledOuter_fst_assoc]
    rw [← integralComponentAt_graphMap_snd]
    rw [← pullback.condition]
    simpa only [Category.assoc] using congrArg (fun m => m ≫ pullback.snd f g)
      (isPullback_correspondenceLeftPulled f g h
        (correspondenceGraphMap f g φ hφ s)).w
  · simp [correspondenceGraphFiberAmbientMap, correspondenceLeftPulledOuter,
      correspondenceTripleTarget, pullback.map]

/-- Base change of the actual graph map along the unchanged last factor. -/
theorem isPullback_correspondenceGraphFiberAmbientMap :
    IsPullback (correspondenceGraphFiberAmbientMap f g h φ hφ)
      (pullback.fst f h) (pullback.fst g h) φ := by
  have H : IsPullback
      (correspondenceGraphFiberAmbientMap f g h φ hφ ≫ pullback.snd g h)
      (pullback.fst f h) h (φ ≫ g) := by
    simpa [correspondenceGraphFiberAmbientMap, pullback.map, hφ] using
      (IsPullback.of_hasPullback f h).flip
  exact H.of_right (by simp [correspondenceGraphFiberAmbientMap, pullback.map])
    (IsPullback.of_hasPullback g h).flip

/-- Admissibility, not flatness over the source, makes an actual finite support
flat over every flat Dedekind parameter of that source. -/
theorem flat_finiteCorrespondenceSupport_to_dedekind
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (q : Y ⟶ Spec (.of R)) [Flat q]
    (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w) :
    Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ q) := by
  let W := (integralComponentAt w).subscheme
  let v : W ⟶ Y := (integralComponentAt w).subschemeι ≫ pullback.fst g h
  haveI : IsIntegral W := isIntegral_integralComponentAt w
  haveI : IsFinite v := hw.1
  have hr : closure ({v (genericPoint W)} : Set Y) = Set.range v := by
    simpa only [Set.image_singleton, genericPoint_closure, Set.image_univ] using
      v.isClosedMap.closure_image_eq_of_continuous v.continuous ({genericPoint W} : Set W)
  have hη : v (genericPoint W) ∈ genericPoints Y := by
    change closure ({v (genericPoint W)} : Set Y) ∈ irreducibleComponents Y
    rw [hr]
    exact hw.2
  apply flat_of_genericPoint_map_eq
  have hq := mem_genericPoints_of_flat q hη
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hq

section AffineLine

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
  (q : Y ⟶ Spec (.of (Polynomial k))) (a : k)
  (hsection : IsPullback φ f q (Scheme.AffineLineFiber.point a))

/-- The outer product is the full literal endpoint of the right adjacent product. -/
def correspondenceEndpointAmbientIso : pullback f h ≅
    Scheme.AffineLineFiber.fiber (pullback.fst g h ≫ q) a :=
  ((isPullback_correspondenceGraphFiberAmbientMap f g h φ hφ).paste_vert hsection).flip.isoPullback

/-- The comparison preserves the actual map into the original right adjacent product. -/
@[reassoc (attr := simp)] theorem correspondenceEndpointAmbientIso_hom_inclusion :
    (correspondenceEndpointAmbientIso f g h φ hφ q a hsection).hom ≫
      Scheme.AffineLineFiber.inclusion (pullback.fst g h ≫ q) a =
        correspondenceGraphFiberAmbientMap f g h φ hφ :=
  IsPullback.isoPullback_hom_snd _

/-- Actual positive pulled Tor vanishes for a Cartesian endpoint and a support
flat only over the affine-line parameter. No whole-source flatness is asserted. -/
theorem isZero_correspondencePulledStalkTor_succ_of_cartesian_endpoint
    [Flat f] [IsLocallyNoetherian X] [IsNormal X]
    [Flat (pullback.fst g h ≫ q)]
    (s : genericPoints X) (w : pullback (C := Scheme) g h)
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ q)]
    (t : correspondenceIncidence f g h (correspondenceGraphMap f g φ hφ s.val) w)
    (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h
        (correspondenceGraphMap f g φ hφ s.val) w t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h
        (correspondenceGraphMap f g φ hφ s.val) w t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h
        (correspondenceGraphMap f g φ hφ s.val) w t)) := by
  let z := correspondenceGraphMap f g φ hφ s.val
  let i := correspondenceLeftPulledInclusion f g h z
  let p := pullback.snd (pullback.snd f g) (pullback.fst g h)
  let o := correspondenceLeftPulledOuter f g h z ≫
    (correspondenceEndpointAmbientIso f g h φ hφ q a hsection).hom
  haveI : IsOpenImmersion (correspondenceLeftPulledOuter f g h z) :=
    isOpenImmersion_correspondenceLeftPulledOuter_graphMap f g h φ hφ s
  haveI : IsOpenImmersion o := by dsimp [o]; infer_instance
  have hi : i ≫ p = o ≫ Scheme.AffineLineFiber.inclusion (pullback.fst g h ≫ q) a := by
    simp only [o, Category.assoc, correspondenceEndpointAmbientIso_hom_inclusion]
    exact correspondenceLeftPulledOuter_graphMap_right f g h φ hφ s.val
  have he : p (correspondenceIncidenceInclusion f g h z w t) =
      (integralComponentAt w).subschemeι (pullback.snd _ _ t) :=
    congrArg (fun m => m t) (correspondenceIncidenceInclusion_snd f g h z w)
  exact Scheme.AffineLineFiber.isZero_pulledStalkTor_succ_of_open_endpoint_of_eq
    (pullback.fst g h ≫ q) a o p i hi (integralComponentAt w)
    (correspondenceIncidenceToLeftPulled f g h z w t)
    (correspondenceIncidenceInclusion f g h z w t)
    (correspondenceIncidenceToRightPulled f g h z w t) (pullback.snd _ _ t)
    (correspondenceIncidence_leftPulled_point_eq f g h z w t)
    (correspondenceIncidence_rightPulled_point_eq f g h z w t) he n

/-- The original finite Euler coefficient is the actual full incidence length.
Its positive terms vanish through the actual original/pulled length comparison;
the degree-zero term uses the existing literal incidence-stalk theorem. -/
theorem correspondenceIncidenceTorCoefficient_eq_length_of_cartesian_endpoint
    [Smooth f] [Smooth g] [Smooth h] [IsLocallyNoetherian X] [IsNormal X]
    [Flat q] (s : genericPoints X) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w)
    (x : genericPoints (correspondenceIncidence f g h
      (correspondenceGraphMap f g φ hφ s.val) w)) :
    correspondenceIncidenceTorCoefficient k f g h
      (correspondenceGraphMap f g φ hφ s.val) w x =
        ((Module.length ((correspondenceIncidence f g h
          (correspondenceGraphMap f g φ hφ s.val) w).presheaf.stalk x.val)
          ((correspondenceIncidence f g h
            (correspondenceGraphMap f g φ hφ s.val) w).presheaf.stalk x.val)).toNat : ℤ) := by
  let z := correspondenceGraphMap f g φ hφ s.val
  haveI := flat_finiteCorrespondenceSupport_to_dedekind g h q w hw
  rw [correspondenceIncidenceTorCoefficient_eq_sum, Finset.sum_eq_single 0]
  · rw [length_correspondenceIncidenceAmbientTor_zero]
    simp
  · intro n hn hn0
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
      have hz := (Module.length_eq_zero_iff
        (R := (correspondenceTripleProduct f g h).presheaf.stalk
          (correspondenceIncidenceInclusion f g h z w x.val))).mpr
        (ModuleCat.isZero_iff_subsingleton.mp
          (isZero_correspondencePulledStalkTor_succ_of_cartesian_endpoint
            f g h φ hφ q a hsection s w x.val n))
      rw [incidenceTor_length_eq_pulledStalkTor k f g h z w x.val (n + 1), hz]
      simp
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

/-- The actual endpoint graph component incidence has the full fundamental
cycle, including its nonreduced generic lengths. This is one incidence term,
not the assembly of a whole finite-flat family. -/
theorem incidenceTorCycle_eq_fundamentalCycle_of_cartesian_endpoint
    [Smooth f] [Smooth g] [Smooth h] [IsLocallyNoetherian X] [IsNormal X]
    [Flat q] (s : genericPoints X) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w)
    [IsNoetherian (correspondenceIncidence f g h
      (correspondenceGraphMap f g φ hφ s.val) w)] :
    incidenceTorCycle f g h (correspondenceGraphMap f g φ hφ s.val) w hw =
      AlgebraicCycle.fundamentalCycle (correspondenceIncidence f g h
        (correspondenceGraphMap f g φ hφ s.val) w) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints (correspondenceIncidence f g h
      (correspondenceGraphMap f g φ hφ s.val) w)
  · rw [incidenceTorCycle_apply_generic f g h _ w hw ⟨x, hx⟩,
      AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨x, hx⟩]
    exact correspondenceIncidenceTorCoefficient_eq_length_of_cartesian_endpoint
      f g h φ hφ q a hsection s w hw ⟨x, hx⟩
  · rw [incidenceTorCycle_apply_of_notMem f g h _ w hw x hx,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem _ x hx]

end AffineLine

end Stacks.Chow
