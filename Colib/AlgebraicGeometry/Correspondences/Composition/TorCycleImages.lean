/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle

/-!
# Admissible generic incidence images and the labelled subgroup sum

Every generic component of the actual incidence has an admissible image in the
outer product. This follows from finiteness of its source projection, native
scheme-theoretic image finiteness, and actual generic-component dominance. The
statement is independent of its Tor coefficient: a zero coefficient, or total
cancellation at a colliding image, does not remove the geometric component.

The actual Tor correspondence is then the literal finite sum in the existing
native finite-correspondence subgroup, indexed by all original generic points.
The integer weight is its actual Tor coefficient times its own residue degree.
No quotient of the generic labels, duplicate cycle model, or injective image map
is introduced. This is the subgroup-valued counterpart of `TorCycle`'s native
cycle sum, needed before expanding either literal nested pairing.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Composition/Incidence/Cycle.lean`, `incidenceCycleAssembly_eq_sum`, and
`Composition/Cycles/LeftComposition.lean`,
`incidenceTorPairing_left_eq_weightedRemaining`. The source's geometric
`FiniteCorrespondenceGenerator` presentation is replaced by the actual native
point and its proved `IsFiniteCorrespondencePoint` property.

Native geometric inputs are the actual dominance theorem in
`ComponentDominance`, the integral-image finiteness proof using Stacks 0AH6 and
02LS in `Pushforward`, and the finite pushforward formula of Stacks 02R4.
No assertion of associativity or of a triple Tor comparison is made here.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- Every original generic incidence image is admissible, independently of all
Tor coefficients and independently of any cancellation between colliding images. -/
@[stacks 0AH6 "properness of the actual scheme-theoretic image is an input",
  stacks 02LS "finite fibres and properness give finiteness of that actual image"]
theorem isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
    [Smooth g] [IsSeparated h] [LocallyOfFiniteType h]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    IsFiniteCorrespondencePoint f h ((correspondenceIncidenceMap f g h z w).base t.val) := by
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  let : IsFinite (correspondenceIncidenceLeft f g h z w) :=
    isFinite_correspondenceIncidenceLeft f g h z w hz hw
  have hfinite : IsFinite (((integralComponentAt t.val).subschemeι ≫
      correspondenceIncidenceMap f g h z w) ≫ pullback.fst f h) := by
    simpa only [Category.assoc, correspondenceIncidenceMap_fst] using
      (inferInstance : IsFinite ((integralComponentAt t.val).subschemeι ≫
        correspondenceIncidenceLeft f g h z w))
  refine ⟨finiteCyclePushforward_isFinite_integralComponentAt
    (correspondenceIncidenceMap f g h z w) (pullback.fst f h) t.val hfinite, ?_⟩
  have hcomponent :
      (correspondenceIncidenceMap f g h z w ≫ pullback.fst f h).base ''
        ((integralComponentAt t.val).support : Set (correspondenceIncidence f g h z w)) ∈
          irreducibleComponents X := by
    simpa only [correspondenceIncidenceMap_fst,
      finiteCyclePushforward_range_integralComponentAt] using
      range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
        f g h z w hz hw t.val t.property
  simpa only [finiteCyclePushforward_range_integralComponentAt] using
    finiteCyclePushforward_image_mem_irreducibleComponents
      (correspondenceIncidenceMap f g h z w) (pullback.fst f h) t.val hcomponent

variable [Smooth g] [Smooth h] [IsSeparated h]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
variable (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

/-- The actual Tor correspondence is the sum of the actual signed image primes
inside the native subgroup. All original generic labels are retained. -/
@[stacks 02R4 "finite pushforward expressed in the native subgroup, indexed by all original \
generic incidence points with their actual residue-field degrees"]
theorem incidenceTorCorrespondence_eq_sum_single :
    incidenceTorCorrespondence f g h z w hz hw =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
          (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
          (correspondenceIncidenceTorCoefficient k f g h z w t *
            ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  apply Subtype.ext
  change (incidenceTorCorrespondence f g h z w hz hw).val =
    (finiteCorrespondences f h).subtype (∑ t : genericPoints (correspondenceIncidence f g h z w),
      singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)))
  rw [map_sum]
  exact incidenceTorCorrespondence_eq_sum f g h z w hz hw

/-- Equivalently, every original generic label contributes its own signed Tor and
degree weight times its actual coefficient-one image prime. -/
theorem incidenceTorCorrespondence_eq_sum_zsmul :
    incidenceTorCorrespondence f g h z w hz hw =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        (correspondenceIncidenceTorCoefficient k f g h z w t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) •
          singleFiniteCorrespondence f h ((correspondenceIncidenceMap f g h z w).base t.val)
            (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t)
            1 := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  rw [incidenceTorCorrespondence_eq_sum_single]
  apply Finset.sum_congr rfl
  intro t ht
  exact singleFiniteCorrespondence_eq_zsmul f h _ _ _

end Stacks.Chow
