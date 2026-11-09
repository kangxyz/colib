/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.GlobalActualTorComparison

/-!
# The finite incidence coefficient in the original pulled-support presentation

The genuine ambient coefficient is the finite alternating sum of the actual Tor
lengths of the two pulled ideal subschemes in the triple product. The existing
degreewise native comparison is applied directly to the complete finite formula.
Finite length and eventual vanishing for these pulled modules follow from proved
ambient facts, not from comparison data or finite-Tor inputs in the hypotheses.
Full scheme structures and local rings are retained.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Composition/Incidence/GlobalAmbientTorComparison.lean` and `Incidence/Tor.lean`.
This is a new coefficient-level consequence of the reconstructed degreewise theorem.
It asserts no equality with a fundamental cycle, unit law, or associativity.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- Every degree of the actual pulled-support Tor has finite length at a generic incidence point. -/
theorem pulledStalkTor_length_ne_top
    (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t.val))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z w t.val))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z w t.val)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z w t.val)) ≠ ⊤ := by
  rw [← incidenceTor_length_eq_pulledStalkTor k f g h z w t.val n]
  exact correspondenceIncidenceTor_length_ne_top f g h z w t n

omit [IsSeparated g] in
/-- The ambient dimension bound also kills the actual pulled-support Tor lengths. -/
theorem pulledStalkTor_length_eq_zero_of_lt (t : correspondenceIncidence f g h z w) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k f g h z w t < n) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z w t))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z w t)) = 0 := by
  rw [← incidenceTor_length_eq_pulledStalkTor k f g h z w t n]
  exact length_correspondenceIncidenceTor_eq_zero_of_lt k f g h z w t n hn

omit [IsSeparated g] in
/-- The actual ambient coefficient is the finite alternating sum in the original
pulled-support presentation, retaining every higher correction and the actual sign. -/
theorem correspondenceIncidenceTorCoefficient_eq_sum_pulledStalkTor
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    correspondenceIncidenceTorCoefficient k f g h z w t =
      ∑ n ∈ Finset.range (correspondenceIncidenceTorDegreeBound k f g h z w t.val + 1),
        (-1 : ℤ) ^ n *
          ((Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
            (correspondenceIncidenceInclusion f g h z w t.val))
            (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
              (correspondenceIncidenceInclusion f g h z w t.val))) n).obj
              (correspondenceIncidenceLeftPulledStalkModule f g h z w t.val)).obj
              (correspondenceIncidenceRightPulledStalkModule f g h z w t.val))).toNat : ℤ) := by
  rw [correspondenceIncidenceTorCoefficient_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [incidenceTor_length_eq_pulledStalkTor k f g h z w t.val n]

end Stacks.Chow
