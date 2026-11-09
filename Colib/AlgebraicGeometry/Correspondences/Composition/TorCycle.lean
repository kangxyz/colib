/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.GenericPushforward
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.ComponentDominance
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward

/-!
# The actual incidence Tor cycle and its finite correspondence

The genuine alternating Tor coefficients of `ActualTorCoefficients` assemble
into a native `AlgebraicCycle` on the actual incidence. Component dominance gives
the finite generic indexing set and proves that every nonzero component covers
an irreducible component of the source. The actual finite incidence map then
pushes this cycle into the existing native finite-correspondence subgroup.

Every original component contributes with its own actual residue-field degree.
The finite coefficient formula sums all contributions with a common image;
neither injectivity of the image map nor positivity of a Tor coefficient is
assumed. There is no caller-supplied coefficient or component-dominance premise.

The base field is arbitrary. The factors are smooth, and the middle and final
structure maps are separated where needed. No connectedness, integrality,
nonemptiness, global Noetherianness, or quasi-compactness of the smooth factors
is assumed. The coefficient cycle itself needs only the second support's
admissibility; the first support's admissibility is used for pushforward.

Implementation provenance: `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/Cycle.lean`
and `Incidence/TorCycle.lean`, in particular `incidenceTorCorrespondence`,
`toIntegralCycle_incidenceTorCorrespondence`, and its coefficient formula.
The source's separate `IntegralCycle` and `Finsupp` models are not retained.
Native Mathlib cycles, Stacks integral components, categorical Tor, and the
native residue-degree pushforward are used directly.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- Smoothness of the middle scheme makes the actual generic incidence set finite.
The finite-fibre argument does not need a compact ambient source. -/
theorem finite_genericPoints_correspondenceIncidence_of_smooth [Smooth g]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w) :
    (genericPoints (correspondenceIncidence f g h z w)).Finite := by
  let : IsNormal Y := isNormal_of_isRegular Y (isRegular_of_smooth_over_field g)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  exact finite_genericPoints_correspondenceIncidence f g h z w hw

variable [Smooth f] [Smooth g] [Smooth h] [IsSeparated g]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The native cycle with the actual finite alternating categorical Tor coefficient
at every generic incidence point and zero at all other points. -/
@[stacks 02QR "finite native generic-point cycle assembly",
  stacks 0AZT "the coefficients are the actual finite alternating Tor lengths from \
correspondenceIncidenceTorCoefficient, not ordinary fundamental-cycle multiplicities"]
def incidenceTorCycle (hw : IsFiniteCorrespondencePoint g h w) :
    AlgebraicCycle (correspondenceIncidence f g h z w) ℤ :=
  AlgebraicCycle.ofGenericCoefficients
    (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw)
    (correspondenceIncidenceTorCoefficient k f g h z w)

/-- The Tor cycle is a literal finite sum over the actual generic incidence points. -/
theorem incidenceTorCycle_eq_sum (hw : IsFiniteCorrespondencePoint g h w) :
    incidenceTorCycle f g h z w hw =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        single t.val (correspondenceIncidenceTorCoefficient k f g h z w t) :=
  AlgebraicCycle.ofGenericCoefficients_eq_sum _ _

/-- Evaluation recovers the genuine alternating Tor coefficient, with its sign. -/
@[simp]
theorem incidenceTorCycle_apply_generic (hw : IsFiniteCorrespondencePoint g h w)
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    incidenceTorCycle f g h z w hw t.val =
      correspondenceIncidenceTorCoefficient k f g h z w t :=
  AlgebraicCycle.ofGenericCoefficients_apply_generic _ _ t

/-- No coefficient is introduced away from the actual generic incidence points. -/
theorem incidenceTorCycle_apply_of_notMem (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∉ genericPoints (correspondenceIncidence f g h z w)) :
    incidenceTorCycle f g h z w hw t = 0 :=
  AlgebraicCycle.ofGenericCoefficients_apply_of_notMem _ _ t ht

/-- The support of the actual Tor cycle is contained in the actual generic set. -/
theorem support_incidenceTorCycle_subset (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCycle f g h z w hw).support ⊆
      genericPoints (correspondenceIncidence f g h z w) :=
  AlgebraicCycle.support_ofGenericCoefficients_subset _ _

/-- Precisely the generic components with nonzero actual Tor coefficient occur. -/
theorem support_incidenceTorCycle (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCycle f g h z w hw).support =
      Subtype.val '' Function.support (correspondenceIncidenceTorCoefficient k f g h z w) :=
  AlgebraicCycle.support_ofGenericCoefficients _ _

/-- The actual Tor cycle has finite support, proved from incidence geometry. -/
theorem finite_support_incidenceTorCycle (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCycle f g h z w hw).support.Finite :=
  AlgebraicCycle.finite_support_ofGenericCoefficients _ _

/-- An empty generic incidence set gives the zero Tor cycle, without a nonemptiness premise. -/
theorem incidenceTorCycle_eq_zero_of_genericPoints_eq_empty
    (hw : IsFiniteCorrespondencePoint g h w)
    (ht : genericPoints (correspondenceIncidence f g h z w) = ∅) :
    incidenceTorCycle f g h z w hw = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro t
  exact incidenceTorCycle_apply_of_notMem f g h z w hw t (by simp [ht])

/-- Actual dominance, not a caller hypothesis, makes every nonzero Tor support
cover the source component of the first correspondence. -/
theorem range_integralComponent_incidenceTorCycle_mem
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w) (ht : incidenceTorCycle f g h z w hw t ≠ 0) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X :=
  range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth f g h z w hz hw t
    (support_incidenceTorCycle_subset f g h z w hw ht)

variable [IsSeparated h]

/-- The actual Tor-weighted incidence correspondence. Finiteness of support and
component admissibility are proved from the two actual finite correspondences. -/
@[stacks 02R4 "finite residue-degree pushforward of the actual incidence Tor cycle"]
def incidenceTorCorrespondence
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    finiteCorrespondences f h :=
  incidencePushforward f g h z w hz hw (incidenceTorCycle f g h z w hw)
    (finite_support_incidenceTorCycle f g h z w hw)
    (range_integralComponent_incidenceTorCycle_mem f g h z w hz hw)

/-- Forgetting admissibility is exactly the actual finite pushforward of the
native incidence Tor cycle. There is no intermediate replacement cycle model. -/
theorem incidenceTorCorrespondence_val
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCorrespondence f g h z w hz hw).val =
      letI : IsFinite (correspondenceIncidenceMap f g h z w) :=
        isFinite_correspondenceIncidenceMap f g h z w hz hw
      finiteCyclePushforward (correspondenceIncidenceMap f g h z w)
        (incidenceTorCycle f g h z w hw) := rfl

/-- Every actual point of the incidence fibre contributes with its own residue degree. -/
theorem incidenceTorCorrespondence_apply
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (y : pullback (C := Scheme) f h) :
    (incidenceTorCorrespondence f g h z w hz hw).val y =
      ∑ᶠ t ∈ (correspondenceIncidenceMap f g h z w).base ⁻¹' {y},
        incidenceTorCycle f g h z w hw t *
          ((correspondenceIncidenceMap f g h z w).residueDegree t : ℤ) :=
  incidencePushforward_apply f g h z w hz hw _ _ _ y

/-- The forgotten correspondence is the sum of all actual degree-weighted generic images. -/
theorem incidenceTorCorrespondence_eq_sum
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCorrespondence f g h z w hz hw).val =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        single ((correspondenceIncidenceMap f g h z w).base t.val)
          (correspondenceIncidenceTorCoefficient k f g h z w t *
            ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)) := by
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  exact finiteCyclePushforward_ofGenericCoefficients _ _ _

/-- All Tor contributions with a common image are added with their separate
actual residue-field degrees. Distinct incidence components may collide. -/
theorem incidenceTorCorrespondence_coefficient
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (y : pullback (C := Scheme) f h) :
    (incidenceTorCorrespondence f g h z w hz hw).val y =
      letI := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        if (correspondenceIncidenceMap f g h z w).base t.val = y then
          correspondenceIncidenceTorCoefficient k f g h z w t *
            ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)
        else 0 := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  calc
    _ = ∑ t : genericPoints (correspondenceIncidence f g h z w),
        if y = (correspondenceIncidenceMap f g h z w).base t.val then
          correspondenceIncidenceTorCoefficient k f g h z w t *
            ((correspondenceIncidenceMap f g h z w).residueDegree t.val : ℤ)
        else 0 :=
      finiteCyclePushforward_ofGenericCoefficients_apply
        (correspondenceIncidenceMap f g h z w)
        (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw)
        (correspondenceIncidenceTorCoefficient k f g h z w) y
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [eq_comm (a := y) (b := (correspondenceIncidenceMap f g h z w).base t.val)]

/-- The actual correspondence has finite point support after all collisions and cancellation. -/
theorem finite_support_incidenceTorCorrespondence
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCorrespondence f g h z w hz hw).val.support.Finite :=
  (incidenceTorCorrespondence f g h z w hz hw).property.1

/-- Each nonzero pushed coefficient is an admissible finite correspondence point. -/
theorem isFiniteCorrespondencePoint_of_incidenceTorCorrespondence_ne_zero
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (y : pullback (C := Scheme) f h)
    (hy : (incidenceTorCorrespondence f g h z w hz hw).val y ≠ 0) :
    IsFiniteCorrespondencePoint f h y :=
  (incidenceTorCorrespondence f g h z w hz hw).property.2 y hy

/-- No pushed support occurs outside the image of the actual generic incidence points. -/
theorem support_incidenceTorCorrespondence_subset
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    (incidenceTorCorrespondence f g h z w hz hw).val.support ⊆
      (correspondenceIncidenceMap f g h z w).base ''
        genericPoints (correspondenceIncidence f g h z w) := by
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  exact (finiteCyclePushforward_support_subset _ _).trans
    (Set.image_mono (support_incidenceTorCycle_subset f g h z w hw))

/-- Empty incidence contributes zero, without imposing a nonempty smooth object. -/
theorem incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (ht : genericPoints (correspondenceIncidence f g h z w) = ∅) :
    incidenceTorCorrespondence f g h z w hz hw = 0 := by
  apply Subtype.ext
  change (incidenceTorCorrespondence f g h z w hz hw).val = 0
  rw [incidenceTorCorrespondence_val,
    incidenceTorCycle_eq_zero_of_genericPoints_eq_empty f g h z w hw ht, map_zero]

end Stacks.Chow
