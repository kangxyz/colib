/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Composition.PointControl

/-!
# All-point control of actual finite-support graph lifts

The existing graph lift is the finite pushforward of the original signed
coefficient cycle. Every point of each surviving lifted support therefore has
an actual preimage under the same finite support map. Prescribed values on a
source fiber transfer to all surviving support points, without closed-point
hypotheses and without requiring positive coefficients.

This supplies the native finite-image point-control step used in
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Points/ChosenGeneratorLift.lean`
(blob `e355c946bccac56ecbabccfae2c22538276575de`) at
`kangxyz/motivic` revision `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z A : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated h]
  (q : Y ⟶ Z) (hq : q ≫ h = g) (hY : (genericPoints Y).Finite)
  (m : A ⟶ pullback f g) [IsFinite m]
  (j : A ⟶ pullback f h) [IsFinite j]
  (hmj : m ≫ pullback.map f g f h (𝟙 X) q (𝟙 _) (by simp)
    (by simpa using hq.symm) = j)

include hmj in
/-- The existing signed graph factorization retains all actual support-point
preimages under its original finite map, including after cancellation. -/
theorem exists_graph_factorization_of_generic_support_map_with_point_lift
    (hA : (genericPoints A).Finite) (c : genericPoints A → ℤ)
    (ha : ∀ a : genericPoints A, IsFiniteCorrespondencePoint f g (m a.val)) :
    ∃ β : finiteCorrespondences f g,
      β.val = finiteCyclePushforward m (AlgebraicCycle.ofGenericCoefficients hA c) ∧
      (incidenceTorPairing f g h β
        (graphCorrespondenceOfComponents g h q hq hY)).val =
        finiteCyclePushforward j (AlgebraicCycle.ofGenericCoefficients hA c) ∧
      ∀ b : pullback (C := Scheme) f g, β.val b ≠ 0 →
        ∀ t : (integralComponentAt b).subscheme,
          ∃ a : A, m a = (integralComponentAt b).subschemeι t := by
  obtain ⟨β, hβ, hcomp⟩ := exists_graph_factorization_of_generic_support_map
    f g h q hq hY m j hmj hA c ha
  refine ⟨β, hβ, hcomp, ?_⟩
  intro b hb t
  rw [hβ] at hb
  exact exists_point_over_integralComponent_of_finiteCyclePushforward_ne_zero
    m (AlgebraicCycle.ofGenericCoefficients hA c) b hb t

omit [Smooth f] [Smooth g] in
/-- A property on a fiber of the actual finite support map passes to every point
of every surviving component of its signed pushforward. -/
theorem target_property_of_finiteCyclePushforward_ne_zero
    (d : AlgebraicCycle A ℤ) (x : X) (Q : Y → Prop)
    (hQ : ∀ a : A, (m ≫ pullback.fst f g) a = x →
      Q ((m ≫ pullback.snd f g) a))
    (b : pullback (C := Scheme) f g) (hb : finiteCyclePushforward m d b ≠ 0)
    (t : (integralComponentAt b).subscheme)
    (ht : ((integralComponentAt b).subschemeι ≫ pullback.fst f g) t = x) :
    Q (((integralComponentAt b).subschemeι ≫ pullback.snd f g) t) := by
  obtain ⟨a, ha⟩ := exists_point_over_integralComponent_of_finiteCyclePushforward_ne_zero
    m d b hb t
  have hs : (m ≫ pullback.fst f g) a = x := by
    change pullback.fst f g (m a) = x
    rw [ha]
    exact ht
  have hv := hQ a hs
  change Q (pullback.snd f g (m a)) at hv
  rw [ha] at hv
  exact hv

end Stacks.Chow
