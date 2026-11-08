/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightGenericImageSupport
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleTorCycle

/-!
# The same actual triple-Tor cycle pushed to the right image

The cycle is the existing actual sixfold triple-Tor cycle, not a new right coefficient
model. Its actual right-image pushforward has the full generic-fibre coefficient formula
with original degrees and vanishes off generic support. Equality with the weighted cycle
is not asserted. References: Stacks 02R4; motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
RightFirstStageWeightedRemainingCoefficient.lean, lines 178-260.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [Smooth g] [Smooth h] [IsSeparated i]

/-- The pushed actual triple cycle vanishes at nongeneric whole-image points by its
proved actual source geometry, not by a caller-supplied support condition. -/
theorem rightTripleTorPushforward_eq_zero_of_not_generic
    [Smooth f] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
      (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x = 0 := by
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  by_contra hne
  obtain ⟨t, ht, htx⟩ := finiteCyclePushforward_support_subset
    (correspondenceTripleToRightImageIncidence f g h i z w v)
    (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) hne
  apply hx
  rw [← htx]
  exact mem_genericPoints_correspondenceTripleToRightImageIncidence f g h i z w v hz hw hv t
    (support_correspondenceTripleIncidenceTorCycle_subset K f g h i z w v hw hv ht)

/-- The actual pushed generic coefficient retains every original triple-fibre label and
its own residue degree. This identifies the literal endpoint of the preceding Euler join. -/
theorem rightTripleTorPushforward_apply_generic
    (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x.1 =
      ∑ᶠ t : {t : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToRightImageIncidence f g h i z w v t.1 = x.1},
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1.1)
            (correspondenceTripleIncidenceTor f g h i z w v t.1.1 n)).toNat : ℤ)) *
          ((correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree t.1.1 : ℤ) := by
  let p := correspondenceTripleToRightImageIncidence f g h i z w v
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  let e : {t : correspondenceTripleIncidence f g h i z w v // p t = x.1} ≃
      {t : genericPoints (correspondenceTripleIncidence f g h i z w v) // p t.1 = x.1} :=
    { toFun := fun t => ⟨⟨t.1,
        mem_genericPoints_of_finite_image p t.1 (t.2.symm ▸ x.2)⟩, t.2⟩
      invFun := fun t => ⟨t.1.1, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [finiteCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  apply finsum_eq_of_bijective e e.bijective
  intro t
  change correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv t.1 *
      (p.residueDegree t.1 : ℤ) =
    correspondenceTripleIncidenceTorCoefficient K f g h i z w v (e t).1 *
      (p.residueDegree t.1 : ℤ)
  have he : (e t).1.1 = t.1 := rfl
  have hvalue := correspondenceTripleIncidenceTorCycle_apply_generic
    K f g h i z w v hw hv (e t).1
  rw [he] at hvalue
  exact congrArg (fun a : ℤ => a * (p.residueDegree t.1 : ℤ)) hvalue

end Stacks.Chow
