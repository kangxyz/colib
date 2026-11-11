/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.ParameterLooping

/-!
# A distinguished-row refinement from actual two-structure interchanges

A based levelwise row interchange constructs a genuine prespectrum whose fixed structure
parameter acts pointwise on its distinguished loop. The original structure maps give a
comparison when the actual two-structure equation holds. Degree zero is constructed from
the original source structure map; no loop-extension property of the source is assumed.
No stability claim follows from this construction alone.
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

/-- The next structure acts on the entire row, followed by the specified genuine interchange. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:30-37"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def rowStructure (k : ℕ) :
    C(Path (E.point (k + 2)) (E.point (k + 2)),
      Path (Path.refl (E.point (k + 3))) (Path.refl (E.point (k + 3)))) :=
  (basedLoopMap (basedLoopMap (q k) (hq k)) (basedLoopMap_refl _ _)).comp
    ((Path.doubleLoopTranspose (E.point (k + 3))).comp
      (basedLoopMap (E.structureMap (k + 2)) (E.map_point (k + 2))))

/-- The row time and the independent spectrum-structure time remain explicit. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:38-42"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem structure_apply (k : ℕ) (γ : Path (E.point (k + 2)) (E.point (k + 2)))
    (r s : unitInterval) :
    rowStructure E q hq k γ r s = q k (E.structureMap (k + 2) (γ s) r) := rfl

/-- The specified structure preserves the actual constant row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:43-54"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem structure_point (k : ℕ) :
    rowStructure E q hq k (Path.refl (E.point (k + 2))) =
      Path.refl (Path.refl (E.point (k + 3))) := by
  apply Path.ext
  funext r
  apply Path.ext
  funext s
  change q k (E.structureMap (k + 2) (E.point (k + 2)) r) = E.point (k + 3)
  rw [E.map_point]
  exact hq k

/-- The actual underlying based map at a fixed independent structure parameter. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:55-59"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def evaluation (k : ℕ) (r : unitInterval) : C(E.space (k + 2), E.space (k + 3)) :=
  ⟨fun x => q k (E.structureMap (k + 2) x r), by fun_prop⟩

include hq in
/-- Each fixed-structure-time evaluation fixes the original basepoint. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:60-66"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem evaluation_point (k : ℕ) (r : unitInterval) :
    evaluation E q k r (E.point (k + 2)) = E.point (k + 3) := by
  change q k (E.structureMap (k + 2) (E.point (k + 2)) r) = E.point (k + 3)
  rw [E.map_point]
  exact hq k

/-- At fixed structure time, the whole distinguished row is mapped by one based map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:67-75"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem structure_row (k : ℕ) (γ : Path (E.point (k + 2)) (E.point (k + 2)))
    (r : unitInterval) :
    rowStructure E q hq k γ r = basedLoopMap (evaluation E q k r)
      (evaluation_point E q hq k r) γ := by
  apply Path.ext
  funext s
  rfl

/-- The distinguished-row target with its explicit degree-zero loop extension. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:76-97"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def spectrum : LoopPrespectrum.{u} where
  space n := Nat.casesOn n
    (TopCat.of (Path (Path.refl (E.point 2)) (Path.refl (E.point 2))))
    (fun k => TopCat.of (Path (E.point (k + 2)) (E.point (k + 2))))
  point n := by
    cases n with
    | zero => exact Path.refl (Path.refl (E.point 2))
    | succ k => exact Path.refl (E.point (k + 2))
  structureMap n := by
    cases n with
    | zero => exact ContinuousMap.id _
    | succ k => exact rowStructure E q hq k
  map_point n := by
    cases n with
    | zero => rfl
    | succ k => exact structure_point E q hq k

variable (hswap : ∀ k (x : E.space (k + 1)) (s t : unitInterval),
  q k (E.structureMap (k + 2) (E.structureMap (k + 1) x s) t) =
    E.structureMap (k + 2) (E.structureMap (k + 1) x t) s)

/-- Original structure maps give a whole comparison, including the actual source degree zero. -/
@[colib_tag "COL-0519", colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:98-119"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def comparison : E ⟶ spectrum E q hq where
  map n := Nat.casesOn n
    ((basedLoopMap (E.structureMap 1) (E.map_point 1)).comp (E.structureMap 0))
    (fun k => E.structureMap (k + 1))
  map_point n := by
    cases n with
    | zero =>
      change basedLoopMap (E.structureMap 1) (E.map_point 1)
        (E.structureMap 0 (E.point 0)) = Path.refl (Path.refl (E.point 2))
      rw [E.map_point, basedLoopMap_refl]
    | succ k => exact E.map_point (k + 1)
  comm n x := by
    cases n with
    | zero => rfl
    | succ k =>
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      exact (hswap k x s r).symm

/-- Positive levels are the unchanged original adjoint structure maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:120-123"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem comparison_succ (k : ℕ) :
    (comparison E q hq hswap).map (k + 1) = E.structureMap (k + 1) := rfl

/-- Degree zero retains both original structure maps and their distinct time coordinates. -/
@[colib_tag "COL-0519", colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinement.lean:124-127"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem comparison_zero (x : E.space 0) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((comparison E q hq hswap).map 0 x) r) s =
      E.structureMap 1 (E.structureMap 0 x r) s := rfl

end Topology.LoopPrespectrum.RowRefinement
