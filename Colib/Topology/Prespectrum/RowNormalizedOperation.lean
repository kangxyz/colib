/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.RowRefinement
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackFamily
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackNaturality

/-!
# Inverse-prefix normalization into an actual distinguished-row refinement

The standard loop normalization is applied to an actual self-track with target the genuine
row-loop prespectrum. Its positive-level structure square follows from the actual based-map
row structure, preserving the original cancellation path. Degree zero is the loop extension of
the positive operation with its explicit parameter transpose. This constructs a whole spectrum
map and does not replace the separate comparison with a specified cofiber null.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {F E : LoopPrespectrum.{u}}
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
  (f : F ⟶ spectrum E q hq) (H : Homotopy f f)

/-- Normalize the complete positive self-track using the original inverse-prefix cancellation. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:35"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
def normalizedStage (k : ℕ) :
    C(F.space (k + 1),
      Path (Path.refl (E.point (k + 2))) (Path.refl (E.point (k + 2)))) :=
  LoopNormalizationPrism.normalized (f.map (k + 1)) (H.levelHomotopy (k + 1)).toHomotopy

/-- The normalization retains the original actual loop, self-track and cancellation word. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:41"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
theorem normalizedStage_apply (k : ℕ) (x : F.space (k + 1)) :
    normalizedStage q hq f H k x = loopNormalizedSelfTrack (f.map (k + 1) x)
      ((H.levelHomotopy (k + 1)).toHomotopy.evalAt x) :=
  LoopNormalizationPrism.normalized_apply _ _ x

/-- Every positive normalized operation preserves the actual source point. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:47"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
theorem normalizedStage_point (k : ℕ) :
    normalizedStage q hq f H k (F.point (k + 1)) =
      Path.refl (Path.refl (E.point (k + 2))) := by
  rw [normalizedStage_apply]
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact loopNormalizedSelfTrack_pointwise id (fun _ : Unit => E.point (k + 2))
    (f.map (k + 1) (F.point (k + 1))) (Path.refl ())
    ((H.levelHomotopy (k + 1)).toHomotopy.evalAt (F.point (k + 1)))
    (Path.refl (Path.refl ()))
    (fun a => congrArg (fun p : Path (E.point (k + 2)) (E.point (k + 2)) => p a)
      (f.map_point (k + 1)))
    (fun b a => congrArg (fun p : Path (E.point (k + 2)) (E.point (k + 2)) => p a)
      (H.at_point (k + 1) b)) t s

/-- The full positive structure square keeps the normalization and row times unchanged. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:65"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
theorem normalizedStage_structure (k : ℕ) (x : F.space (k + 1))
    (r t s : unitInterval) :
    evaluation E q k r (normalizedStage q hq f H k x t s) =
      normalizedStage q hq f H (k + 1) (F.structureMap (k + 1) x r) t s := by
  rw [normalizedStage_apply, normalizedStage_apply]
  apply loopNormalizedSelfTrack_pointwise (evaluation E q k r) id
  · intro a
    have hf := congrArg (fun p => p r) (f.comm (k + 1) x)
    exact (congrArg (fun p : Path (E.point (k + 3)) (E.point (k + 3)) => p a) hf).symm
  · intro b a
    exact (congrArg (fun p : Path (E.point (k + 3)) (E.point (k + 3)) => p a)
      (H.comm (k + 1) b x r)).symm

/-- The complete normalized operation, with its explicit zero-level parameter transpose. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:79"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
def normalizedOperation : F ⟶ parameterLooping (spectrum E q hq) where
  map n := Nat.casesOn n
    ((Path.doubleLoopTranspose (Path.refl (E.point 2))).comp
      ((basedLoopMap (normalizedStage q hq f H 0)
        (normalizedStage_point q hq f H 0)).comp (F.structureMap 0)))
    (normalizedStage q hq f H)
  map_point n := by
    cases n with
    | zero =>
      change Path.doubleLoopTranspose _
        (basedLoopMap (normalizedStage q hq f H 0) (normalizedStage_point q hq f H 0)
          (F.structureMap 0 (F.point 0))) = _
      rw [F.map_point]
      rw [basedLoopMap_refl, Path.doubleLoopTranspose_refl]
      rfl
    | succ k => exact normalizedStage_point q hq f H k
  comm n x := by
    cases n with
    | zero =>
      apply Path.ext
      funext r
      apply Path.ext
      funext t
      rfl
    | succ k =>
      apply Path.ext
      funext r
      apply Path.ext
      funext t
      apply Path.ext
      funext s
      exact (normalizedStage_structure q hq f H k x r t s).symm

/-- Positive levels are the literal original normalized first-row self-tracks. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:113"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
theorem normalizedOperation_succ (k : ℕ) (x : F.space (k + 1)) :
    (normalizedOperation q hq f H).map (k + 1) x = normalizedStage q hq f H k x := rfl

/-- Degree zero displays the forward unit time before the independent original input-loop time. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperation.lean:117"
  "adaptation" "Original structure-compatible normalized operation and explicit zero level"]
theorem normalizedOperation_zero (x : F.space 0)
    (t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap ((normalizedOperation q hq f H).map 0 x) t) a) s =
        normalizedStage q hq f H 0 (F.structureMap 0 x a) t s := rfl

end Topology.LoopPrespectrum.RowRefinement

namespace Topology.LoopPrespectrum.RowRefinement

attribute [colib_tag "COL-0549"] normalizedOperation
attribute [colib_tag "COL-0549"] normalizedOperation_succ
attribute [colib_tag "COL-0549"] normalizedOperation_zero

end Topology.LoopPrespectrum.RowRefinement
