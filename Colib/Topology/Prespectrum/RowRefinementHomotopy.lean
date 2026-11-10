/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RowRefinementMap
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Whole homotopies on actual distinguished rows

A prescribed whole homotopy acts pointwise on the row refinement when every time slice
preserves the actual row interchange. The homotopy retains the independent row and time
coordinates, including both loop coordinates at degree zero. Endpoint squares alone do not
supply the required whole-time hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  {a b : E ⟶ F}
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
  (hb : ∀ k x, qF k (b.map (k + 3) x) = b.map (k + 3) (qE k x))
  (H : Homotopy a b)
  (hH : ∀ k t x, qF k (H.level (k + 3) (t, x)) =
    H.level (k + 3) (t, qE k x))

/-- The specified whole row-natural homotopy, including the explicit degree-zero double loop. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementHomotopy.lean:38-65"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def homotopy : Homotopy (map qE qF hE hF a ha) (map qE qF hE hF b hb) where
  level n := Nat.casesOn n (H.parameterLooping.parameterLooping.level 2)
    (fun k => H.parameterLooping.level (k + 2))
  at_zero n x := by
    cases n with
    | zero => exact H.parameterLooping.parameterLooping.at_zero 2 x
    | succ k => exact H.parameterLooping.at_zero (k + 2) x
  at_one n x := by
    cases n with
    | zero => exact H.parameterLooping.parameterLooping.at_one 2 x
    | succ k => exact H.parameterLooping.at_one (k + 2) x
  at_point n t := by
    cases n with
    | zero => exact H.parameterLooping.parameterLooping.at_point 2 t
    | succ k => exact H.parameterLooping.at_point (k + 2) t
  comm n t x r := by
    cases n with
    | zero => rfl
    | succ k =>
      change Path (E.point (k + 2)) (E.point (k + 2)) at x
      apply Path.ext
      funext s
      change H.level (k + 3) (t, qE k (E.structureMap (k + 2) (x s) r)) =
        qF k (F.structureMap (k + 2) (H.level (k + 2) (t, x s)) r)
      rw [← hH]
      exact congrArg (qF k) (H.comm (k + 2) t (x s) r)

/-- Positive levels keep the whole original homotopy at the unchanged row coordinate. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementHomotopy.lean:66-71"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem homotopy_succ (k : ℕ)
    (γ : Path (E.point (k + 2)) (E.point (k + 2))) (t r : unitInterval) :
    Path.toContinuousMap ((homotopy qE qF hE hF ha hb H hH).level (k + 1) (t, γ)) r =
      H.level (k + 2) (t, γ r) := rfl

/-- The whole degree-zero homotopy keeps both row parameters independent of its time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementHomotopy.lean:72-78"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem homotopy_zero
    (γ : Path (Path.refl (E.point 2)) (Path.refl (E.point 2))) (t r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((homotopy qE qF hE hF ha hb H hH).level 0 (t, γ)) r) s =
      H.level 2 (t, γ r s) := rfl

/-- The actual zero map remains the zero map on both positive rows and the double zero row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementHomotopy.lean:79-90"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem map_zero
    (hz : ∀ k x, qF k ((zeroHom E F).map (k + 3) x) =
      (zeroHom E F).map (k + 3) (qE k x)) :
    map qE qF hE hF (zeroHom E F) hz = zeroHom (spectrum E qE hE) (spectrum F qF hF) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero => apply Path.ext; funext r; apply Path.ext; funext s; rfl
  | succ k => apply Path.ext; funext r; rfl

end Topology.LoopPrespectrum.RowRefinement
