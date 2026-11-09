/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycleImages

/-!
# Literal nested Tor pairings as labelled weighted remaining correspondences

Both actual bracketings on three prime correspondences expand over the original
first-stage generic incidence points. Every term retains the actual first-stage
Tor coefficient, its actual residue-field degree, and the actual remaining Tor
correspondence of that image prime with the third input. No collision of image
points removes or identifies an original generic label.

These are exact expansions of the two nested native pairings, including arbitrary
signed multiplicities of the three inputs. They are not an associativity proof.
The left and right expressions use different genuine incidence schemes, different
generic indexing sets, and different remaining Tor correspondences. Comparing
their weighted remaining cycles requires a genuine triple-intersection theorem,
which is neither assumed nor asserted by this module.

Original source: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Cycles/LeftComposition.lean`,
Git blob `bb359ac96107367ce6acce86ebc152f78309ecb3`, specifically the theorem
`incidenceTorPairing_left_eq_weightedRemaining`. The later source results using
`tripleTorCorrespondence_eq_weightedRemaining` are outside the implemented scope.
The right expansion and signed variants use the same native additive-map argument;
no claim is made that the cited source has an identically named right theorem.

Actual coefficients and residue degrees retain the precise Stacks 0AZT and 02R4
scope documented in `TorCycle`. The generic images' admissibility is proved by
`TorCycleImages`, independently of whether their Tor weights vanish. The field
is arbitrary, and smooth objects may be disconnected, empty, or non-quasi-compact.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable (i : W ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [Smooth h] [Smooth i]
variable [IsSeparated g] [IsSeparated h] [IsSeparated i]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
variable (v : pullback (C := Scheme) h i)
variable (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
variable (hv : IsFiniteCorrespondencePoint h i v)

/-- The left first-stage Tor correspondence expands into all original generic
labels, each followed by its actual remaining Tor correspondence. -/
theorem incidenceTorPairing_left_eq_weightedRemaining :
    incidenceTorPairing f h i (incidenceTorCorrespondence f g h z w hz hw)
      (singleFiniteCorrespondence h i v hv 1) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) •
          incidenceTorCorrespondence f h i
            ((correspondenceIncidenceMap f g h z w).base t.val) v
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            hv := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  rw [incidenceTorCorrespondence_eq_sum_single]
  change (incidenceTorPairing f h i).flip (singleFiniteCorrespondence h i v hv 1)
    (∑ t : genericPoints (correspondenceIncidence f g h z w),
      singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [AddMonoidHom.flip_apply, incidenceTorPairing_single, mul_one]

/-- The right first-stage Tor correspondence likewise retains all original labels,
with its own actual coefficients and degrees before the remaining composition. -/
theorem incidenceTorPairing_right_eq_weightedRemaining :
    incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
      (incidenceTorCorrespondence g h i w v hw hv) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient k g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.val : ℤ)) •
          incidenceTorCorrespondence f g i z
            ((correspondenceIncidenceMap g h i w v).base t.val) hz
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t) := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  rw [incidenceTorCorrespondence_eq_sum_single, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [incidenceTorPairing_single, one_mul]

/-- Literally nesting the actual pairing on the left gives the labelled weighted
remaining sum. This statement is not a comparison with the right bracket. -/
theorem incidenceTorPairing_left_single_one_eq_weightedRemaining :
    incidenceTorPairing f h i
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
        (singleFiniteCorrespondence g h w hw 1))
      (singleFiniteCorrespondence h i v hv 1) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) •
          incidenceTorCorrespondence f h i
            ((correspondenceIncidenceMap f g h z w).base t.val) v
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            hv := by
  rw [incidenceTorPairing_single_one]
  exact incidenceTorPairing_left_eq_weightedRemaining f g h i z w v hz hw hv

/-- Literally nesting the actual pairing on the right gives its own labelled
weighted remaining sum, without identifying the two generic indexing schemes. -/
theorem incidenceTorPairing_right_single_one_eq_weightedRemaining :
    incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
      (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
        (singleFiniteCorrespondence h i v hv 1)) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient k g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.val : ℤ)) •
          incidenceTorCorrespondence f g i z
            ((correspondenceIncidenceMap g h i w v).base t.val) hz
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t) := by
  rw [incidenceTorPairing_single_one]
  exact incidenceTorPairing_right_eq_weightedRemaining f g h i z w v hz hw hv

/-- All three input signs and every first-stage geometric weight survive in the
literal left nested pairing. -/
theorem incidenceTorPairing_left_single_eq_weightedRemaining (a b c : ℤ) :
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
            hv := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  rw [incidenceTorPairing_single, incidenceTorPairing_zsmul_left,
    singleFiniteCorrespondence_eq_zsmul h i v hv c, incidenceTorPairing_zsmul_right,
    smul_smul, incidenceTorPairing_left_eq_weightedRemaining]
  simp only [Finset.smul_sum, smul_smul]

/-- All three input signs and every first-stage geometric weight survive in the
literal right nested pairing, with its distinct original generic labels. -/
theorem incidenceTorPairing_right_single_eq_weightedRemaining (a b c : ℤ) :
    incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz a)
      (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw b)
        (singleFiniteCorrespondence h i v hv c)) =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        ((a * b * c) * (correspondenceIncidenceTorCoefficient k g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.val : ℤ))) •
          incidenceTorCorrespondence f g i z
            ((correspondenceIncidenceMap g h i w v).base t.val) hz
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t) := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  rw [singleFiniteCorrespondence_eq_zsmul f g z hz a, incidenceTorPairing_zsmul_left,
    incidenceTorPairing_single, incidenceTorPairing_zsmul_right, smul_smul,
    incidenceTorPairing_right_eq_weightedRemaining]
  simp only [Finset.smul_sum, smul_smul, mul_assoc]

end Stacks.Chow
