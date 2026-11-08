/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedComponentEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedCycle

/-!
# The actual whole-family Euler is the actual weighted remaining-cycle coefficient

At every generic whole-image incidence point, apply the same original regular
remaining list to the canonical whole finite Tor family. Its all-degree signed
Euler is the coefficient of the actual labelled weighted remaining native cycle.
Each full quotient Euler is attached to its actual remaining incidence Tor cycle,
including zero when the component has no point above the chosen point.

The canonical triple total-Euler comparison and nongeneric support argument are
separate obligations. This theorem does not accept either as a hypothesis or
assert full associativity. The original implementation target is the local
coefficient chain in motivic FirstStageWeightedRemainingCoefficient.lean,
revision a6805c4a87cdfd7717dd7a94039246a167f15380, verified blob
3ae09238bac659f48c9e4beb21004af8f02ffd84, lines 107-245.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "R" =>
  correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" =>
  correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v x₀)
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingFiniteTorModule f g h i z w v x.1
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

include hz hw hv

/-- Canonical whole-family Euler equals the actual weighted remaining native-cycle coefficient.
No module family, localization identity, or weighted comparison is provided by the caller. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedCycle
    [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV] {r : ℕ}
    (s : Fin r → A) (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  rw [finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedComponents
    K f g h i z w v hz hw x s hs, correspondenceLeftWeightedRemainingCycle_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun a : ℤ =>
    (correspondenceIncidenceTorCoefficient K f g h z w t *
      ((correspondenceIncidenceMap f g h z w).residueDegree t.1 : ℤ)) * a)
  exact seqEuler_correspondenceRemainingImageComponent_eq_pushforward_TorCycle
    K f g h i z w v hv t.1 x.1 x.2 s hsr hs

end Stacks.Chow
