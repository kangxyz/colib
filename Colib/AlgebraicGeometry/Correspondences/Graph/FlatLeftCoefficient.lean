/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.LeftProjectedEndpoint
public import Colib.AlgebraicGeometry.Intersection.FlatProjectedStalkTor

/-!
# The actual incidence coefficient for a flat left graph

A normal-source graph component projects openly to the full source. Its actual
projection to the right adjacent product is therefore flat when the original
map is flat. The actual flat-projection Tor comparison gives all positive Tor
vanishing without a flatness assumption on any second support component.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g] [Flat φ]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A flat actual left graph has vanishing positive pulled-support Tor. -/
theorem isZero_correspondencePulledStalkTor_succ_of_flat_graph [Flat f]
    (s : genericPoints X) (w : pullback g h)
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
  haveI : IsOpenImmersion (correspondenceLeftPulledOuter f g h z) :=
    isOpenImmersion_correspondenceLeftPulledOuter_graphMap f g h φ hφ s
  haveI : Flat (correspondenceGraphFiberAmbientMap f g h φ hφ) :=
    MorphismProperty.of_isPullback
      (isPullback_correspondenceGraphFiberAmbientMap f g h φ hφ).flip inferInstance
  haveI : Flat (i ≫ p) := by
    rw [show i ≫ p = correspondenceLeftPulledOuter f g h z ≫
      correspondenceGraphFiberAmbientMap f g h φ hφ from
        correspondenceLeftPulledOuter_graphMap_right f g h φ hφ s.val]
    infer_instance
  have he : p (correspondenceIncidenceInclusion f g h z w t) =
      (integralComponentAt w).subschemeι (pullback.snd _ _ t) :=
    congrArg (fun m => m t) (correspondenceIncidenceInclusion_snd f g h z w)
  exact Scheme.Hom.isZero_torStalkComap_succ_of_flat_composite_of_eq p i
    (integralComponentAt w) (correspondenceIncidenceToLeftPulled f g h z w t)
    (correspondenceIncidenceInclusion f g h z w t)
    (correspondenceIncidenceToRightPulled f g h z w t) (pullback.snd _ _ t)
    (correspondenceIncidence_leftPulled_point_eq f g h z w t)
    (correspondenceIncidence_rightPulled_point_eq f g h z w t) he n

/-- The original signed Tor Euler coefficient equals the full incidence self-length. -/
theorem correspondenceIncidenceTorCoefficient_eq_length_of_flat_graph
    [Smooth f] [Smooth g] [Smooth h] (s : genericPoints X) (w : pullback g h)
    (x : genericPoints (correspondenceIncidence f g h
      (correspondenceGraphMap f g φ hφ s.val) w)) :
    correspondenceIncidenceTorCoefficient k f g h
      (correspondenceGraphMap f g φ hφ s.val) w x =
        ((Module.length ((correspondenceIncidence f g h
          (correspondenceGraphMap f g φ hφ s.val) w).presheaf.stalk x.val)
          ((correspondenceIncidence f g h
            (correspondenceGraphMap f g φ hφ s.val) w).presheaf.stalk x.val)).toNat : ℤ) := by
  let z := correspondenceGraphMap f g φ hφ s.val
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
          (isZero_correspondencePulledStalkTor_succ_of_flat_graph
            f g h φ hφ s w x.val n))
      rw [incidenceTor_length_eq_pulledStalkTor k f g h z w x.val (n + 1), hz]
      simp
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

/-- The native graph incidence cycle is the whole fundamental cycle. -/
theorem incidenceTorCycle_eq_fundamentalCycle_of_flat_graph
    [Smooth f] [Smooth g] [Smooth h] (s : genericPoints X) (w : pullback g h)
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
    exact correspondenceIncidenceTorCoefficient_eq_length_of_flat_graph f g h φ hφ s w ⟨x, hx⟩
  · rw [incidenceTorCycle_apply_of_notMem f g h _ w hw x hx,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem _ x hx]

end Stacks.Chow
