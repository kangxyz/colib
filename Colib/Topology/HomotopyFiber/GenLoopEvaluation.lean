/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.Sequence
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrack
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
# Evaluation of a homotopy fiber of based cubes

A point of the homotopy fiber of based-cube postcomposition consists of an original cube
and an entire null path in the target cube space. Evaluating these two coordinates gives
a based cube in the original path-space homotopy fiber. This map is continuous for the
original compact-open and subtype topologies and is defined using `liftGenLoop`.

The loop-inclusion formula retains the original null-path time and every spatial coordinate.
Its first-coordinate currying consequence uses no coordinate permutation or sign change.
-/

/-! Implementation provenance: `Quillen/Topology/HomotopyFiber/GenLoopEvaluation.lean:32-154`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology

noncomputable section

open scoped Topology unitInterval

universe u v

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)

local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)

/-- Uncurry the whole null path of a point in the original cube-space homotopy fiber. -/
def genLoopEvaluationNullhomotopy (w : HomotopyFiber F B) :
    (GenLoop.postcomp f h w.val.1).val.HomotopyRel (B).val
      (Cube.boundary (Fin (n + 1))) where
  toFun tz := w.val.2 tz.1 tz.2
  continuous_toFun := by fun_prop
  map_zero_left z := congrArg (fun p : GenLoop (Fin (n + 1)) Y y ↦ p z) w.property.1
  map_one_left z := congrArg (fun p : GenLoop (Fin (n + 1)) Y y ↦ p z) w.property.2
  prop' t z hz :=
    ((w.val.2 t).property z hz).trans ((GenLoop.postcomp f h w.val.1).property z hz).symm

/-- The nullhomotopy retains both the original path time and the entire cube input. -/
@[simp] theorem genLoopEvaluationNullhomotopy_apply (w : HomotopyFiber F B)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    genLoopEvaluationNullhomotopy f y x h n w (t, z) = w.val.2 t z := rfl

/-- Evaluate a fiber point of based cubes as a cube in the original homotopy fiber. -/
def genLoopEvaluation :
    C(HomotopyFiber F B,
      GenLoop (Fin (n + 1)) (HomotopyFiber f y) (basepoint f y x h)) where
  toFun w := liftGenLoop f y x h w.val.1 (genLoopEvaluationNullhomotopy f y x h n w)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · change Continuous (fun wz : HomotopyFiber F B × (Fin (n + 1) → unitInterval) ↦
        wz.1.val.1 wz.2)
      fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous
        (fun wzt : (HomotopyFiber F B × (Fin (n + 1) → unitInterval)) × unitInterval ↦
          wzt.1.1.val.2 wzt.2 wzt.1.2)
      fun_prop

/-- The evaluated fiber cube has exactly the supplied original source cube. -/
@[simp] theorem genLoopEvaluation_source (w : HomotopyFiber F B)
    (z : Fin (n + 1) → unitInterval) :
    (genLoopEvaluation f y x h n w z).val.1 = w.val.1 z := rfl

/-- Its stored path is the original null path evaluated at the same spatial point. -/
@[simp] theorem genLoopEvaluation_path (w : HomotopyFiber F B)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (genLoopEvaluation f y x h n w z).val.2 t = w.val.2 t z := rfl

/-- Evaluation is based on the whole spatial boundary, including every stored path time. -/
theorem genLoopEvaluation_boundary (w : HomotopyFiber F B)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopEvaluation f y x h n w z = basepoint f y x h :=
  (genLoopEvaluation f y x h n w).property z hz

/-- Projection of the complete evaluated cube recovers the original cube strictly. -/
@[simp] theorem genLoopPostcomp_genLoopEvaluation (w : HomotopyFiber F B) :
    GenLoop.postcomp (projection f y) (projection_basepoint f y x h)
      (genLoopEvaluation f y x h n w) = w.val.1 :=
  genLoopPostcomp_liftGenLoop f y x h _ _

/-- The actual constant fiber point evaluates to the original constant fiber cube. -/
@[simp] theorem genLoopEvaluation_basepoint :
    genLoopEvaluation f y x h n
      (basepoint F B GenLoop.const (GenLoop.postcomp_const f h)) = GenLoop.const := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- A displayed relative nullhomotopy gives exactly the pre-existing `liftGenLoop` cube. -/
theorem genLoopEvaluation_liftGenLoop (p : GenLoop (Fin (n + 1)) X x)
    (H : (GenLoop.postcomp f h p).val.HomotopyRel (B).val
      (Cube.boundary (Fin (n + 1)))) :
    genLoopEvaluation f y x h n
      ⟨(p, (genLoopPathOfHomotopyRel H).toContinuousMap),
        (genLoopPathOfHomotopyRel H).source, (genLoopPathOfHomotopyRel H).target⟩ =
      liftGenLoop f y x h p H := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- Evaluation commutes literally with original loop inclusion, with both times unchanged. -/
theorem genLoopEvaluation_loopInclusion (L : Path B B) :
    genLoopEvaluation f y x h n
      (loopInclusion F B GenLoop.const (GenLoop.postcomp_const f h) L) =
      GenLoop.postcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
        (genLoopOfBasedPath L) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- The original first-coordinate curry recovers this same evaluated loop-inclusion cube. -/
theorem genLoopEvaluation_loopCurry (L : Path B B) :
    GenLoop.postcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (loopCurry (loopUncurry (genLoopOfBasedPath L))) =
      genLoopEvaluation f y x h n
        (loopInclusion F B GenLoop.const (GenLoop.postcomp_const f h) L) := by
  rw [loopCurry_loopUncurry]
  exact (genLoopEvaluation_loopInclusion f y x h n L).symm

end Topology.HomotopyFiber

attribute [colib_ref "quillen"
    "Quillen/Topology/HomotopyFiber/GenLoopEvaluation.lean:32-154"
    "adaptation"
    "Actual path-space fiber evaluation with every original spatial coordinate and path time"]
  Topology.HomotopyFiber.genLoopEvaluation_loopInclusion
  Topology.HomotopyFiber.genLoopEvaluation_loopCurry
