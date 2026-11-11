/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RowRefinement
public import Colib.Topology.Prespectrum.RowInterchangeParameterLooping

/-!
# Actual parameter-loop and distinguished-row coordinate interchange

The row refinement of a parameter-looped spectrum is isomorphic to the parameter loop of
its row refinement. Positive levels transpose the old loop and row coordinates. Degree zero
moves the old loop past both explicit row coordinates. The spectrum-structure coordinate is
never identified with any of these parameters.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable (E : LoopPrespectrum.{u})
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))

/-- Move the old parameter loop outside the genuine distinguished row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementParameterLooping.lean:30-55"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def parameterLoopingComparison :
    spectrum (parameterLooping E) (RowInterchange.parameterLoop q hq)
      (RowInterchange.parameterLoop_point q hq) ⟶ parameterLooping (spectrum E q hq) where
  map n := Nat.casesOn n
    ((Path.doubleLoopTranspose (Path.refl (E.point 2))).comp
      (basedLoopMap (Path.doubleLoopTranspose (E.point 2)) (Path.doubleLoopTranspose_refl _)))
    (fun k => Path.doubleLoopTranspose (E.point (k + 2)))
  map_point n := by
    cases n with
    | zero =>
      apply Path.ext; funext t; apply Path.ext; funext r; apply Path.ext; funext s; rfl
    | succ k => exact Path.doubleLoopTranspose_refl _
  comm n γ := by
    cases n with
    | zero =>
      apply Path.ext; funext a
      apply Path.ext; funext t
      apply Path.ext; funext s
      rfl
    | succ k =>
      apply Path.ext; funext a
      apply Path.ext; funext t
      apply Path.ext; funext s
      rfl

/-- Move the old parameter loop back inside both explicit distinguished-row levels. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementParameterLooping.lean:56-82"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def parameterLoopingInverse :
    parameterLooping (spectrum E q hq) ⟶
      spectrum (parameterLooping E) (RowInterchange.parameterLoop q hq)
        (RowInterchange.parameterLoop_point q hq) where
  map n := Nat.casesOn n
    ((basedLoopMap (Path.doubleLoopTranspose (E.point 2)) (Path.doubleLoopTranspose_refl _)).comp
      (Path.doubleLoopTranspose (Path.refl (E.point 2))))
    (fun k => Path.doubleLoopTranspose (E.point (k + 2)))
  map_point n := by
    cases n with
    | zero =>
      apply Path.ext; funext r; apply Path.ext; funext s; apply Path.ext; funext t; rfl
    | succ k => exact Path.doubleLoopTranspose_refl _
  comm n γ := by
    cases n with
    | zero =>
      apply Path.ext; funext a
      apply Path.ext; funext s
      apply Path.ext; funext t
      rfl
    | succ k =>
      apply Path.ext; funext a
      apply Path.ext; funext s
      apply Path.ext; funext t
      rfl

/-- This comparison is a genuine coordinate isomorphism, without a stability assumption. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementParameterLooping.lean:83-101"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def parameterLoopingIso :
    spectrum (parameterLooping E) (RowInterchange.parameterLoop q hq)
      (RowInterchange.parameterLoop_point q hq) ≅ parameterLooping (spectrum E q hq) where
  hom := parameterLoopingComparison E q hq
  inv := parameterLoopingInverse E q hq
  hom_inv_id := by
    apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
    cases n with
    | zero =>
      apply Path.ext; funext r; apply Path.ext; funext s; apply Path.ext; funext t; rfl
    | succ k => apply Path.ext; funext s; apply Path.ext; funext t; rfl
  inv_hom_id := by
    apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
    cases n with
    | zero =>
      apply Path.ext; funext t; apply Path.ext; funext r; apply Path.ext; funext s; rfl
    | succ k => apply Path.ext; funext t; apply Path.ext; funext s; rfl

/-- The positive comparison retains row and old-loop time in the stated order. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementParameterLooping.lean:102-108"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem parameterLoopingComparison_succ (k : ℕ)
    (γ : Path (Path.refl (E.point (k + 2))) (Path.refl (E.point (k + 2))))
    (t s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((parameterLoopingComparison E q hq).map (k + 1) γ) t) s = γ s t := rfl

/-- At degree zero the old loop passes both original row coordinates. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementParameterLooping.lean:109-114"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem parameterLoopingComparison_zero
    (γ : Path (Path.refl (Path.refl (E.point 2))) (Path.refl (Path.refl (E.point 2))))
    (t r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((parameterLoopingComparison E q hq).map 0 γ) t) r) s = γ r s t := rfl

end Topology.LoopPrespectrum.RowRefinement
