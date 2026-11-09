/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightGenericImageSupport

/-!
# Nongeneric vanishing for the actual right weighted remaining cycle

Each original G,H generic label has its proved admissible Y-to-W image support. The actual
remaining pair maps generics to original source generics. The finite right-image source
map reflects them. Each labelled remaining pushforward, and therefore the weighted cycle,
vanishes off the right-image generic set. No support premise or flatness of F over Y is used.
References: Stacks 0F32 and 02R4; motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
RightFirstStageWeightedRemainingCoefficient.lean, lines 214-260.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {K : Type u} [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Each actual remaining-pair generic lands in the genuine right-image generic set. -/
theorem mem_genericPoints_correspondenceRightRemainingPairToImageIncidence
    [Smooth f] [Smooth g] [Smooth h] [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : genericPoints (correspondenceIncidence g h i w v))
    (a : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t.1))
    (ha : a ∈ genericPoints
      (correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t.1))) :
    correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1 a ∈
      genericPoints (correspondenceRightImageIncidence f g h i z w v) := by
  let := isFinite_correspondenceRightImageIncidenceSource f g h i z w v hz hw hv
  apply mem_genericPoints_of_finite_image
    (correspondenceRightImageIncidenceSource f g h i z w v)
  rw [← Scheme.Hom.comp_apply, correspondenceRightRemainingPairToImageIncidence_source]
  exact mem_genericPoints_correspondenceIncidenceLeft_of_smooth f g i z _ hz
    (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t) a ha

/-- Every actual remaining Tor-cycle pushforward vanishes off generic support. -/
theorem rightRemainingPairTorPushforward_eq_zero_of_not_generic
    [Smooth f] [Smooth g] [Smooth h] [Smooth i]
    [IsSeparated g] [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : genericPoints (correspondenceIncidence g h i w v))
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    finiteCyclePushforward (correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1)
      (incidenceTorCycle f g i z (correspondenceIncidenceMap g h i w v t.1)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t)) x =
          0 := by
  by_contra hne
  obtain ⟨a, ha, hax⟩ := finiteCyclePushforward_support_subset
    (correspondenceRightRemainingPairToImageIncidence f g h i z w v t.1)
    (incidenceTorCycle f g i z (correspondenceIncidenceMap g h i w v t.1)
      (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic g h i w v hw hv t)) hne
  apply hx
  rw [← hax]
  exact mem_genericPoints_correspondenceRightRemainingPairToImageIncidence
    f g h i z w v hz hw hv t a
    (support_incidenceTorCycle_subset f g i z _ _ ha)

/-- The full labelled right weighted cycle is zero at every nongeneric whole-image point. -/
theorem correspondenceRightWeightedRemainingCycle_eq_zero_of_not_generic
    [Smooth f] [Smooth g] [Smooth h] [Smooth i]
    [IsSeparated g] [IsSeparated h] [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    correspondenceRightWeightedRemainingCycle f g h i z w v hw hv x = 0 := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  rw [correspondenceRightWeightedRemainingCycle_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [rightRemainingPairTorPushforward_eq_zero_of_not_generic f g h i z w v hz hw hv t x hx,
    mul_zero]

end Stacks.Chow
