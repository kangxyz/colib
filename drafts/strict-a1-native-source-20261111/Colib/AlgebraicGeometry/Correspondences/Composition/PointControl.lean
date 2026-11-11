/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle

/-!
# All-point provenance for the native incidence Tor correspondence

A surviving coefficient of the actual finite pushforward gives an incidence point.
Closedness of that finite image then lifts every point of the surviving integral
support, not merely its generic point. Integer signs, Tor coefficients, residue
degrees and image collisions remain those of the native cycle.

Adapted from `kangxyz/motivic` at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/PointControl.lean`, blob
`a406042039c0a29d86e865a2ec06b2214e3b4d66`. This leaf supplies the geometric
provenance step; the signed biadditive extension belongs to the next leaf.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- Every actual point of a surviving integral support of a finite pushforward
lies in the finite map's range. The input cycle has arbitrary integer signs. -/
theorem exists_point_over_integralComponent_of_finiteCyclePushforward_ne_zero
    {A B : Scheme.{u}} (r : A ⟶ B) [IsFinite r]
    (d : AlgebraicCycle A ℤ) (b : B) (hb : finiteCyclePushforward r d b ≠ 0)
    (c : (integralComponentAt b).subscheme) :
    ∃ a : A, r a = (integralComponentAt b).subschemeι c := by
  have hb' : b ∈ (finiteCyclePushforward r d).support := hb
  obtain ⟨a, _, ha⟩ := finiteCyclePushforward_support_subset r d hb'
  have hr : b ∈ Set.range r := ⟨a, ha⟩
  have hc : (integralComponentAt b).subschemeι c ∈ closure ({b} : Set B) := by
    rw [← coe_support_integralComponentAt, ← (integralComponentAt b).range_subschemeι]
    exact Set.mem_range_self c
  exact closure_minimal (Set.singleton_subset_iff.mpr hr)
    r.isClosedMap.isClosed_range hc

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth g] [Smooth h] [IsSeparated h]

/-- All points of a surviving output support come from the actual incidence
scheme carrying the native alternating Tor cycle. -/
theorem exists_incidence_point_of_incidenceTorCorrespondence_ne_zero
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (b : pullback (C := Scheme) f h)
    (hb : (incidenceTorCorrespondence f g h z w hz hw).val b ≠ 0)
    (c : (integralComponentAt b).subscheme) :
    ∃ a : correspondenceIncidence f g h z w,
      correspondenceIncidenceMap f g h z w a = (integralComponentAt b).subschemeι c := by
  letI : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  apply exists_point_over_integralComponent_of_finiteCyclePushforward_ne_zero
    (correspondenceIncidenceMap f g h z w) (incidenceTorCycle f g h z w hw) b
  exact hb

end Stacks.Chow
