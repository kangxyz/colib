/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.RowNormalizationLevels

/-!
# Whole-spectrum normalization using the prescribed null in a row-compatible target

The original inverse-prefix normalized operation is compared with the original null/unit/null
map by an actual structure-compatible homotopy. Both zero and positive levels use the same
parameterized prism, with the explicit degree-zero loop extension. No homotopy-group detection,
point-set inverse of a stable map, or replacement contraction enters the construction.
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

/-- The complete prism compares the original normalization to the prescribed null-conjugation. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalization.lean:33"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def normalizationHomotopy :
    Homotopy (normalizedOperation q hq f H) (H.nullLoopMap N) where
  level n := Nat.casesOn n (normalizationZero q hq f H N) (normalizationStage q hq f H N)
  at_zero n x := by
    cases n with
    | zero =>
      apply Path.ext
      funext t
      apply Path.ext
      funext a
      apply Path.ext
      funext s
      change normalizationZero q hq f H N (0, x) t a s = _
      rw [normalizationZero_apply, normalizationStage_zero]
      rfl
    | succ k => exact normalizationStage_zero q hq f H N k x
  at_one n x := by
    cases n with
    | zero =>
      apply Path.ext
      funext t
      apply Path.ext
      funext a
      apply Path.ext
      funext s
      change normalizationZero q hq f H N (1, x) t a s = _
      rw [normalizationZero_apply, normalizationStage_one]
      exact congrArg (fun p : Path (E.point 2) (E.point 2) => p s)
        ((H.conjugateToZero N).comm 0 t x a)
    | succ k => exact normalizationStage_one q hq f H N k x
  at_point n r := by
    cases n with
    | zero => exact normalizationZero_point q hq f H N r
    | succ k => exact normalizationStage_point q hq f H N k r
  comm n r x a := by
    cases n with
    | zero =>
      apply Path.ext
      funext t
      rfl
    | succ k =>
      apply Path.ext
      funext t
      apply Path.ext
      funext s
      exact (normalizationStage_structure q hq f H N k x a r t s).symm

/-- Positive levels retain the original prism, normalization, and row coordinates. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalization.lean:81"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_succ (k : ℕ) (x : F.space (k + 1))
    (r t s : unitInterval) :
    Path.toContinuousMap
      (Path.toContinuousMap ((normalizationHomotopy q hq f H N).level (k + 1) (r, x)) t) s =
        normalizationStage q hq f H N k (r, x) t s := rfl

/-- Degree zero explicitly retains the original source-structure coordinate as well. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalization.lean:88"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_zero (x : F.space 0) (r t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap ((normalizationHomotopy q hq f H N).level 0 (r, x)) t) a) s =
        normalizationStage q hq f H N 0 (r, F.structureMap 0 x a) t s := rfl

end Topology.LoopPrespectrum.RowRefinement

attribute [colib_tag "COL-0552"]
  Topology.LoopPrespectrum.RowRefinement.normalizationHomotopy
