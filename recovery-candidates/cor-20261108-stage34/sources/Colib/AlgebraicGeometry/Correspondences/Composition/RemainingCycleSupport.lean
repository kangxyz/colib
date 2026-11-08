/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericImageSupport

/-!
# Actual remaining and triple generic support on the whole image

Finite correspondence support projections over smooth schemes are universally open by
native Stacks 0F32. Their base changes and composites send actual generic points to source
component generic points. The finite whole-image source map reflects those generic points,
since its fibres are discrete. Thus both actual triple generics and every original labelled
remaining-incidence generic map to generic points of the whole image incidence.

No openness, flatness, reduction, normality, or component hypothesis is imposed on the whole
image or the triple-to-image map. Normality is used only for the original smooth factors,
component by component. The argument works over arbitrary fields and disconnected schemes.

References: Stacks 0F32 (quasi-finite component dominance implies universal openness),
040F (open morphisms lift generalizations), 02R4 (finite pushforward support), and
Mazza--Voevodsky--Weibel, Lemma 1.7, printed page 5. Implementation comparison:
independent motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean, lines 205-245.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {K : Type u} [Field K]

variable {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Each original generic first-incidence label has its actual remaining generic image
inside the whole image generic set. Coincident labels are not identified. -/
theorem mem_genericPoints_correspondenceRemainingPairToImageIncidence
    [Smooth f] [Smooth g] [Smooth h] [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : genericPoints (correspondenceIncidence f g h z w))
    (a : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t.1) v)
    (ha : a ∈ genericPoints
      (correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t.1) v)) :
    correspondenceRemainingPairToImageIncidence f g h i z w v t.1 a ∈
      genericPoints (correspondenceLeftImageIncidence f g h i z w v) := by
  let := isFinite_correspondenceLeftImageIncidenceSource f g h i z w v hz hw hv
  apply mem_genericPoints_of_finite_image
    (correspondenceLeftImageIncidenceSource f g h i z w v)
  have hsource : correspondenceRemainingPairToImageIncidence f g h i z w v t.1 ≫
      correspondenceLeftImageIncidenceSource f g h i z w v =
      correspondenceIncidenceLeft f h i (correspondenceIncidenceMap f g h z w t.1) v := by
    rw [← correspondenceLeftImageIncidenceMap_fst, ← Category.assoc,
      correspondenceRemainingPairToImageIncidence_map, correspondenceIncidenceMap_fst]
  rw [← Scheme.Hom.comp_apply, hsource]
  exact mem_genericPoints_correspondenceIncidenceLeft_of_smooth f h i _ v
    (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic f g h z w hz hw t) hv a ha

/-- Every actual labelled remaining Tor pushforward is zero at a nongeneric whole-image
point, before taking its signed first-stage weight. -/
theorem remainingPairTorPushforward_eq_zero_of_not_generic
    [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : genericPoints (correspondenceIncidence f g h z w))
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    finiteCyclePushforward (correspondenceRemainingPairToImageIncidence f g h i z w v t.1)
      (incidenceTorCycle f h i (correspondenceIncidenceMap f g h z w t.1) v hv) x = 0 := by
  by_contra hne
  obtain ⟨a, ha, hax⟩ := finiteCyclePushforward_support_subset
    (correspondenceRemainingPairToImageIncidence f g h i z w v t.1)
    (incidenceTorCycle f h i (correspondenceIncidenceMap f g h z w t.1) v hv) hne
  apply hx
  rw [← hax]
  exact mem_genericPoints_correspondenceRemainingPairToImageIncidence
    f g h i z w v hz hw hv t a
    (support_incidenceTorCycle_subset f h i _ v hv ha)

/-- The entire literal weighted remaining cycle vanishes at every nongeneric whole-image
point, with no support condition supplied by the caller. -/
theorem correspondenceLeftWeightedRemainingCycle_eq_zero_of_not_generic
    [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x = 0 := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  rw [correspondenceLeftWeightedRemainingCycle_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [remainingPairTorPushforward_eq_zero_of_not_generic f g h i z w v hz hw hv t x hx,
    mul_zero]

end Stacks.Chow
