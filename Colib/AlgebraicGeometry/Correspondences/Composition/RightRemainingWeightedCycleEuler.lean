/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedComponentEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedCycle

/-!
# Actual whole right Tor-family Euler equals the literal weighted remaining cycle

All retained original G,H labels are regrouped through their actual finite image.
The full image-component quotient absorbs the actual exterior multiplicity, and
its original Y-list Euler is the literal remaining F,image(G,H) Tor pushforward.
The actual smooth factors supply finite type; no image-flatness, reverse
admissibility, support equality or coefficient comparison is a premise.
Reference: motivic a6805c4, Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b; native Stacks 02RG and 02R4.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence

universe u

namespace Stacks.Chow

attribute [local instance 100000] HasDerivedCategory.standard

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hz hw hv

/-- The actual full right family computes the original labelled weighted remaining coefficient. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedCycle
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hsr : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M n))) =
        correspondenceRightWeightedRemainingCycle f g h i z w v hw hv x.1 := by
  dsimp only
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let : LocallyOfFiniteType
      (((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g) := by
    infer_instance
  let : LocallyOfFiniteType
      (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) := by infer_instance
  let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
  rw [finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedComponents
    K f g h i z w v hz hw hv x s hs, correspondenceRightWeightedRemainingCycle_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun a : ℤ =>
    (correspondenceIncidenceTorCoefficient K g h i w v t *
      ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) * a)
  exact seqEuler_correspondenceRightRemainingImageComponent_eq_pushforward_TorCycle
    K f g h i z w v hw hv t x.1 x.2 s hsr hs

end Stacks.Chow
