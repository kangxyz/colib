/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.RowNormalizedOperation
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizationPrismRelative
public import Colib.Topology.Prespectrum.HomotopyLoop

/-!
# Whole levels of normalization in a genuine distinguished-row target

The prescribed whole null and self-track give the parameterized original normalization prism.
The fixed-structure-time based maps of the row refinement preserve that prism. The degree-zero
extension uses the actual source structure map and displays its independent input-loop time.
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
  (N : Homotopy f (zeroHom F (spectrum E q hq)))

/-- The full positive-level prism retains the original normalization and prescribed null. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:34"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def normalizationStage (k : ℕ) :
    C(unitInterval × F.space (k + 1),
      Path (Path.refl (E.point (k + 2))) (Path.refl (E.point (k + 2)))) :=
  (LoopNormalizationPrism.normalizationHomotopy (f.map (k + 1))
    (H.levelHomotopy (k + 1)).toHomotopy (N.levelHomotopy (k + 1)).toHomotopy).toContinuousMap

/-- The whole normalization prism fixes the actual original point. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:41"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationStage_point (k : ℕ) (r : unitInterval) :
    normalizationStage q hq f H N k (r, F.point (k + 1)) =
      Path.refl (Path.refl (E.point (k + 2))) :=
  LoopNormalizationPrism.normalizationHomotopy_fixed _ _ _ _ (f.map_point (k + 1))
    (fun t => H.at_point (k + 1) t) (fun t => N.at_point (k + 1) t) r

/-- The initial face is the unchanged inverse-prefix normalized operation. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:48"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationStage_zero (k : ℕ) (x : F.space (k + 1)) :
    normalizationStage q hq f H N k (0, x) = normalizedStage q hq f H k x :=
  (LoopNormalizationPrism.normalizationHomotopy _ _ _).apply_zero x

/-- The terminal face is the original null/unit/null loop with its original clocks. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:53"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationStage_one (k : ℕ) (x : F.space (k + 1)) :
    normalizationStage q hq f H N k (1, x) = (H.nullLoopMap N).map (k + 1) x := by
  change LoopNormalizationPrism.normalizationHomotopy _ _ _ (1, x) = _
  rw [ContinuousMap.Homotopy.apply_one]
  apply Path.ext
  funext t
  rfl

/-- The positive spectrum square retains all three prism coordinates and the structure time. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:62"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationStage_structure (k : ℕ) (x : F.space (k + 1))
    (a r t s : unitInterval) :
    evaluation E q k a (normalizationStage q hq f H N k (r, x) t s) =
      normalizationStage q hq f H N (k + 1) (r, F.structureMap (k + 1) x a) t s := by
  apply LoopNormalizationPrism.normalizationHomotopy_pointwise (evaluation E q k a) id
  · intro b
    have hf := congrArg (fun p => p a) (f.comm (k + 1) x)
    exact (congrArg (fun p : Path (E.point (k + 3)) (E.point (k + 3)) => p b) hf).symm
  · intro b c
    exact (congrArg (fun p : Path (E.point (k + 3)) (E.point (k + 3)) => p c)
      (H.comm (k + 1) b x a)).symm
  · intro b c
    exact (congrArg (fun p : Path (E.point (k + 3)) (E.point (k + 3)) => p c)
      (N.comm (k + 1) b x a)).symm

/-- The full zero-level prism extends the positive prism over the original source structure. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:78"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def normalizationZero :
    C(unitInterval × F.space 0,
      Path (Path.refl (Path.refl (E.point 2))) (Path.refl (Path.refl (E.point 2)))) where
  toFun z := Path.doubleLoopTranspose (Path.refl (E.point 2)) {
    toFun a := normalizationStage q hq f H N 0 (z.1, F.structureMap 0 z.2 a)
    continuous_toFun := by fun_prop
    source' := by
      rw [Path.source]
      exact normalizationStage_point q hq f H N 0 z.1
    target' := by
      rw [Path.target]
      exact normalizationStage_point q hq f H N 0 z.1 }
  continuous_toFun := by
    apply (Path.doubleLoopTranspose (Path.refl (E.point 2))).continuous.comp
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × F.space 0) × unitInterval =>
      normalizationStage q hq f H N 0 (z.1.1, F.structureMap 0 z.1.2 z.2))
    fun_prop

/-- The unit, source-loop and coefficient-row coordinates remain in their specified order. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:98"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationZero_apply (x : F.space 0) (r t a s : unitInterval) :
    normalizationZero q hq f H N (r, x) t a s =
      normalizationStage q hq f H N 0 (r, F.structureMap 0 x a) t s := rfl

/-- The degree-zero prism fixes the original point at every time. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizationLevels.lean:103"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationZero_point (r : unitInterval) :
    normalizationZero q hq f H N (r, F.point 0) =
      Path.refl (Path.refl (Path.refl (E.point 2))) := by
  apply Path.ext
  funext t
  apply Path.ext
  funext a
  apply Path.ext
  funext s
  rw [normalizationZero_apply, F.map_point]
  exact congrArg (fun p => p t s) (normalizationStage_point q hq f H N 0 r)

end Topology.LoopPrespectrum.RowRefinement
