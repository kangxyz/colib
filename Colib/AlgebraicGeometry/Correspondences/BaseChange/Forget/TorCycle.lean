/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Single
public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.TorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle

/-!
# Native incidence Tor cycles after forgetting an unramified field base

The actual generic-point equivalence reindexes the native incidence Tor cycle.
The whole-incidence isomorphism has residue degree one, so its finite pushforward
preserves every signed coefficient. Composing the actual final incidence maps
then proves the native prime-pair composition comparison.

No caller supplies a Tor comparison, generic coefficient, or composition law.
The proof uses the actual finite pushforward, including any collisions under
the final source-target projection. Empty and disconnected schemes are allowed.

Adapted from motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Composition.lean`.
The old separate generator and cycle models are replaced by native signed cycles.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k L : Type u} [Field k] [Field L]
  {X Y Z : Scheme.{u}} (r : Spec (.of L) ⟶ Spec (.of k))
  (f : X ⟶ Spec (.of L)) (g : Y ⟶ Spec (.of L)) (h : Z ⟶ Spec (.of L))
  [IsSeparated r] [FormallyUnramified r] [LocallyOfFiniteType r]
  [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  [Smooth (g ≫ r)] [Smooth (h ≫ r)]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- Every native generic incidence coefficient survives the actual isomorphism pushforward. -/
theorem forgetBase_incidenceTorCycle (hw : IsFiniteCorrespondencePoint g h w) :
    finiteCyclePushforward (forgetBaseIncidenceMap r f g h z w)
        (incidenceTorCycle f g h z w hw) =
      incidenceTorCycle (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)
        (isFiniteCorrespondencePoint_forgetBase r g h w hw) := by
  classical
  let hw' := isFiniteCorrespondencePoint_forgetBase r g h w hw
  let G := forgetBaseIncidenceGenericsEquiv r f g h z w
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    (f ≫ r) (g ≫ r) (h ≫ r)
    (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) hw').fintype
  rw [incidenceTorCycle_eq_sum, incidenceTorCycle_eq_sum, map_sum]
  calc
    (∑ t : genericPoints (correspondenceIncidence f g h z w),
        finiteCyclePushforward (forgetBaseIncidenceMap r f g h z w)
          (single t.val (correspondenceIncidenceTorCoefficient L f g h z w t))) =
      ∑ t : genericPoints (correspondenceIncidence f g h z w),
        single (G t).val
          (correspondenceIncidenceTorCoefficient k (f ≫ r) (g ≫ r) (h ≫ r)
            (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) (G t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [finiteCyclePushforward_single_of_isClosedImmersion,
        forgetBase_correspondenceIncidenceTorCoefficient]
      rfl
    _ = _ := G.sum_comp (fun t =>
      (single t.val
        (correspondenceIncidenceTorCoefficient k (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) t) :
        AlgebraicCycle (correspondenceIncidence (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)) ℤ))

/-- The actual native prime-pair composition commutes with finite scalar forgetting. -/
theorem finiteCorrespondencesForgetBase_incidenceTorCorrespondence
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    finiteCorrespondencesForgetBase r f h (incidenceTorCorrespondence f g h z w hz hw) =
      incidenceTorCorrespondence (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)
        (isFiniteCorrespondencePoint_forgetBase r f g z hz)
        (isFiniteCorrespondencePoint_forgetBase r g h w hw) := by
  let hz' := isFiniteCorrespondencePoint_forgetBase r f g z hz
  let hw' := isFiniteCorrespondencePoint_forgetBase r g h w hw
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  let : IsFinite (correspondenceIncidenceMap (f ≫ r) (g ≫ r) (h ≫ r)
      (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)) :=
    isFinite_correspondenceIncidenceMap (f ≫ r) (g ≫ r) (h ≫ r)
      (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) hz' hw'
  apply Subtype.ext
  change finiteCyclePushforward (forgetBaseProductMap r f h)
      (finiteCyclePushforward (correspondenceIncidenceMap f g h z w)
        (incidenceTorCycle f g h z w hw)) =
    finiteCyclePushforward
      (correspondenceIncidenceMap (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w))
      (incidenceTorCycle (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) hw')
  rw [← forgetBase_incidenceTorCycle r f g h z w hw,
    finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply]
  have hpush {A B : Scheme.{u}} (p q : A ⟶ B) [IsFinite p] [IsFinite q]
      (hpq : p = q) (c : AlgebraicCycle A ℤ) :
      finiteCyclePushforward p c = finiteCyclePushforward q c := by
    subst q
    rfl
  exact hpush _ _ (forgetBaseIncidenceMap_map r f g h z w).symm _

end Stacks.Chow
