/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycleImages

/-! Source-only tests: generic-image admissibility precedes Tor coefficients,
labelled native subgroup sums, colliding images, and zero-weight components. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
variable (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

-- No outer smoothness or nonzero coefficient is required for actual image geometry.
example [Smooth g] [IsSeparated h] [LocallyOfFiniteType h]
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    IsFiniteCorrespondencePoint f h ((correspondenceIncidenceMap f g h z w).base t.val) :=
  isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t

variable [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

example :
    incidenceTorCorrespondence f g h z w hz hw =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
          (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
          (correspondenceIncidenceTorCoefficient k f g h z w t *
            ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) :=
  incidenceTorCorrespondence_eq_sum_single f g h z w hz hw

example :
    incidenceTorCorrespondence f g h z w hz hw =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) •
          singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            1 :=
  incidenceTorCorrespondence_eq_sum_zsmul f g h z w hz hw

-- Even when a Tor coefficient vanishes, the original image is geometrically admissible.
example (t : genericPoints (correspondenceIncidence f g h z w))
    (ht : correspondenceIncidenceTorCoefficient k f g h z w t = 0) :
    IsFiniteCorrespondencePoint f h ((correspondenceIncidenceMap f g h z w).base t.val) ∧
      singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) = 0 := by
  refine ⟨isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t, ?_⟩
  apply Subtype.ext
  simp [singleFiniteCorrespondence, ht]

-- Equal images add their two independent signed contributions. No equality of labels is assumed.
example (t t' : genericPoints (correspondenceIncidence f g h z w)) (a b : ℤ)
    (himage : (correspondenceIncidenceMap f g h z w).base t.val =
      (correspondenceIncidenceMap f g h z w).base t'.val) :
    singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t) a +
      singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t'.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t') b =
      singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
        (a + b) := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y = (correspondenceIncidenceMap f g h z w).base t.val <;>
    simp [singleFiniteCorrespondence, single_apply, ← himage, hy]
