/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.WeightedPairing

/-! Source-only tests of the two distinct actual brackets, retaining all original
generic labels, their signed Tor coefficients, and residue degrees. Not associativity. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped BigOperators

universe u

variable {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable (i : W ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [Smooth h] [Smooth i]
variable [IsSeparated g] [IsSeparated h] [IsSeparated i]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
variable (v : pullback (C := Scheme) h i)
variable (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
variable (hv : IsFiniteCorrespondencePoint h i v)

example :
    incidenceTorPairing f h i (incidenceTorCorrespondence f g h z w hz hw)
      (singleFiniteCorrespondence h i v hv 1) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) •
          incidenceTorCorrespondence f h i
            ((correspondenceIncidenceMap f g h z w).base t.val) v
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            hv :=
  incidenceTorPairing_left_eq_weightedRemaining f g h i z w v hz hw hv

example :
    incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
      (incidenceTorCorrespondence g h i w v hw hv) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient k g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.val : ℤ)) •
          incidenceTorCorrespondence f g i z
            ((correspondenceIncidenceMap g h i w v).base t.val) hz
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t) :=
  incidenceTorPairing_right_eq_weightedRemaining f g h i z w v hz hw hv

-- The left literal nested pairing keeps arbitrary signed input multiplicities.
example (a b c : ℤ) :
    incidenceTorPairing f h i
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz a)
        (singleFiniteCorrespondence g h w hw b))
      (singleFiniteCorrespondence h i v hv c) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        ((a * b * c) * (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ))) •
          incidenceTorCorrespondence f h i
            ((correspondenceIncidenceMap f g h z w).base t.val) v
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            hv :=
  incidenceTorPairing_left_single_eq_weightedRemaining f g h i z w v hz hw hv a b c

-- The right literal nested pairing has its own genuine first-stage incidence indexing set.
example (a b c : ℤ) :
    incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz a)
      (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw b)
        (singleFiniteCorrespondence h i v hv c)) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        ((a * b * c) * (correspondenceIncidenceTorCoefficient k g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.val : ℤ))) •
          incidenceTorCorrespondence f g i z
            ((correspondenceIncidenceMap g h i w v).base t.val) hz
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t) :=
  incidenceTorPairing_right_single_eq_weightedRemaining f g h i z w v hz hw hv a b c

-- Concrete signs produce -30 times each original left geometric weight.
example :
    incidenceTorPairing f h i
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz (-2))
        (singleFiniteCorrespondence g h w hw 3))
      (singleFiniteCorrespondence h i v hv 5) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        ((-30 : ℤ) * (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ))) •
          incidenceTorCorrespondence f h i
            ((correspondenceIncidenceMap f g h z w).base t.val) v
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            hv := by
  simpa using
    incidenceTorPairing_left_single_eq_weightedRemaining f g h i z w v hz hw hv (-2) 3 5

-- An empty left incidence contributes zero before any comparison with the right bracket.
example [IsEmpty (correspondenceIncidence f g h z w)] :
    incidenceTorPairing f h i
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
        (singleFiniteCorrespondence g h w hw 1))
      (singleFiniteCorrespondence h i v hv 1) = 0 := by
  rw [incidenceTorPairing_single_one,
    incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty f g h z w hz hw
      (Set.eq_empty_of_isEmpty _), incidenceTorPairing_zero_left]

-- An empty right incidence is handled independently on the other bracketing.
example [IsEmpty (correspondenceIncidence g h i w v)] :
    incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
      (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
        (singleFiniteCorrespondence h i v hv 1)) = 0 := by
  rw [incidenceTorPairing_single_one,
    incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty g h i w v hw hv
      (Set.eq_empty_of_isEmpty _), incidenceTorPairing_zero_right]
