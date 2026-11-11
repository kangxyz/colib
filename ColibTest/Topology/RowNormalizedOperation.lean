/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.RowNormalizedOperation

open CategoryTheory Topology Topology.LoopPrespectrum Topology.LoopPrespectrum.RowRefinement
open scoped Topology unitInterval
noncomputable section
universe u
variable {F E : LoopPrespectrum.{u}}
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
  (f : F ⟶ spectrum E q hq) (H : Homotopy f f)

example (k : ℕ) (x : F.space (k + 1)) :
    normalizedStage q hq f H k x = loopNormalizedSelfTrack (f.map (k + 1) x)
      ((H.levelHomotopy (k + 1)).toHomotopy.evalAt x) :=
  normalizedStage_apply q hq f H k x

example (k : ℕ) :
    normalizedStage q hq f H k (F.point (k + 1)) =
      Path.refl (Path.refl (E.point (k + 2))) :=
  normalizedStage_point q hq f H k

example (k : ℕ) (x : F.space (k + 1))
    (r t s : unitInterval) :
    evaluation E q k r (normalizedStage q hq f H k x t s) =
      normalizedStage q hq f H (k + 1) (F.structureMap (k + 1) x r) t s :=
  normalizedStage_structure q hq f H k x r t s

example (k : ℕ) (x : F.space (k + 1)) :
    (normalizedOperation q hq f H).map (k + 1) x = normalizedStage q hq f H k x :=
  normalizedOperation_succ q hq f H k x

example (x : F.space 0)
    (t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap ((normalizedOperation q hq f H).map 0 x) t) a) s =
        normalizedStage q hq f H 0 (F.structureMap 0 x a) t s :=
  normalizedOperation_zero q hq f H x t a s

example : F ⟶ parameterLooping (spectrum E q hq) := normalizedOperation q hq f H
