/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle

/-! Source-only semantic tests for actual coefficients, finite support, dominance,
all colliding image contributions, and empty incidence. No compiler has been run. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped BigOperators

universe u

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [Smooth h] [IsSeparated g]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
variable (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

-- The native cycle is constructed without a supplied coefficient or finite generic-set premise.
example : AlgebraicCycle (correspondenceIncidence f g h z w) ℤ :=
  incidenceTorCycle f g h z w hw

example : (incidenceTorCycle f g h z w hw).support.Finite :=
  finite_support_incidenceTorCycle f g h z w hw

-- Literal signed finite Tor lengths, not the ordinary local length of the incidence.
example (t : genericPoints (correspondenceIncidence f g h z w)) :
    incidenceTorCycle f g h z w hw t.val =
      ∑ n ∈ Finset.range (correspondenceIncidenceTorDegreeBound k f g h z w t.val + 1),
        (-1 : ℤ) ^ n *
          ((Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
              (correspondenceIncidenceAmbientInclusion f g h z w t.val))
            (correspondenceIncidenceTor f g h z w t.val n)).toNat : ℤ) := by
  rw [incidenceTorCycle_apply_generic, correspondenceIncidenceTorCoefficient_eq_sum]

-- Actual dominance supplies the source-component condition without an extra hcomp argument.
example (t : correspondenceIncidence f g h z w)
    (ht : incidenceTorCycle f g h z w hw t ≠ 0) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X :=
  range_integralComponent_incidenceTorCycle_mem f g h z w hz hw t ht

example (ht : genericPoints (correspondenceIncidence f g h z w) = ∅) :
    incidenceTorCycle f g h z w hw = 0 :=
  incidenceTorCycle_eq_zero_of_genericPoints_eq_empty f g h z w hw ht

variable [IsSeparated h]

example : finiteCorrespondences f h := incidenceTorCorrespondence f g h z w hz hw

example :
    (incidenceTorCorrespondence f g h z w hz hw).val =
      letI : IsFinite (correspondenceIncidenceMap f g h z w) :=
        isFinite_correspondenceIncidenceMap f g h z w hz hw
      finiteCyclePushforward (correspondenceIncidenceMap f g h z w)
        (incidenceTorCycle f g h z w hw) :=
  incidenceTorCorrespondence_val f g h z w hz hw

-- Every generic preimage is counted, including coincident images and negative coefficients.
open Classical in
example (y : pullback (C := Scheme) f h) :
    (incidenceTorCorrespondence f g h z w hz hw).val y =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        if (correspondenceIncidenceMap f g h z w).base t.val = y then
          correspondenceIncidenceTorCoefficient k f g h z w t *
            ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)
        else 0 :=
  incidenceTorCorrespondence_coefficient f g h z w hz hw y

example (y : pullback (C := Scheme) f h)
    (hy : (incidenceTorCorrespondence f g h z w hz hw).val y ≠ 0) :
    IsFiniteCorrespondencePoint f h y :=
  isFiniteCorrespondencePoint_of_incidenceTorCorrespondence_ne_zero f g h z w hz hw y hy

example (ht : genericPoints (correspondenceIncidence f g h z w) = ∅) :
    incidenceTorCorrespondence f g h z w hz hw = 0 :=
  incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty f g h z w hz hw ht

-- A geometric empty incidence is covered without manufacturing a point or a component.
example [IsEmpty (correspondenceIncidence f g h z w)] :
    incidenceTorCorrespondence f g h z w hz hw = 0 := by
  apply incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
  exact Set.eq_empty_of_isEmpty _
