/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowCylinderRealization
public import Colib.Topology.Path.DoubleLoopTranspose

/-!
# A prespectrum retaining one distinguished original S-row

The positive levels are loops on the next genuine S-stage. Their structure maps retain the
loop parameter internally, followed by the actual two-row transpose. The degree-zero space
is the original loop extension of the positive sequence. Thus the original structure maps give
an actual comparison from the original S-prespectrum. The row transpose remains visible, and
no identification with ordinary loop-tail stabilization is asserted.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/RowLoopPrespectrum.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
row transpose, based maps, independent time coordinates and hypotheses are retained.
The existing native wide category of zero-preserving exact maps supplies the original models. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- The whole positive structure map, with the coefficient row kept internal. -/
def rowLoopStageStructure (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    C(Path (stagePoint (k + 1) W) (stagePoint (k + 1) W),
      Path (Path.refl (stagePoint (k + 2) W)) (Path.refl (stagePoint (k + 2) W))) :=
  (basedLoopMap
    (basedLoopMap ⟨stageRowSwapHomeomorph k W, (stageRowSwapHomeomorph k W).continuous⟩
      (stageRowSwapHomeomorph_point k W))
    (basedLoopMap_refl _ _)).comp
      ((Path.doubleLoopTranspose (stagePoint (k + 2) W)).comp
        (basedLoopMap (stageLoopMap (k + 1) W) (stageLoopMap_point (k + 1) W)))

/-- All row and structure times occur in their original distinct positions. -/
theorem rowLoopStageStructure_apply (k : ℕ) (W : WideSubcategory preservesZero.{u})
    (γ : Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)) (r s : unitInterval) :
    rowLoopStageStructure k W γ r s =
      stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W (γ s) r) := rfl

/-- The positive structure map preserves the actual constant loop. -/
theorem rowLoopStageStructure_point (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    rowLoopStageStructure k W (Path.refl (stagePoint (k + 1) W)) =
      Path.refl (Path.refl (stagePoint (k + 2) W)) := by
  apply Path.ext
  funext r
  apply Path.ext
  funext s
  change stageRowSwapHomeomorph k W
    (stageLoopMap (k + 1) W (stagePoint (k + 1) W) r) = stagePoint (k + 2) W
  rw [stageLoopMap_point]
  exact stageRowSwapHomeomorph_point k W

/-- At fixed structure time, the underlying actual based map on the next S-stage. -/
def rowLoopStructureEvaluation (k : ℕ) (W : WideSubcategory preservesZero.{u}) (r : unitInterval) :
    C(stageSpace (k + 1) W, stageSpace (k + 2) W) :=
  ⟨fun x => stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W x r), by fun_prop⟩

/-- The fixed-structure-time evaluation preserves the original point. -/
theorem rowLoopStructureEvaluation_point (k : ℕ) (W : WideSubcategory preservesZero.{u})
    (r : unitInterval) :
    rowLoopStructureEvaluation k W r (stagePoint (k + 1) W) = stagePoint (k + 2) W := by
  change stageRowSwapHomeomorph k W
    (stageLoopMap (k + 1) W (stagePoint (k + 1) W) r) = stagePoint (k + 2) W
  rw [stageLoopMap_point]
  exact stageRowSwapHomeomorph_point k W

/-- Each fixed structure time acts by an actual based map on the entire coefficient loop. -/
theorem rowLoopStageStructure_row (k : ℕ) (W : WideSubcategory preservesZero.{u})
    (γ : Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)) (r : unitInterval) :
    rowLoopStageStructure k W γ r =
      basedLoopMap (rowLoopStructureEvaluation k W r)
        (rowLoopStructureEvaluation_point k W r) γ := by
  apply Path.ext
  funext s
  rfl

/-- The genuine distinguished-row prespectrum, with its specified degree-zero loop extension. -/
def rowLoopPrespectrum (W : WideSubcategory preservesZero.{u}) : LoopPrespectrum.{u} where
  space n := Nat.casesOn n
    (TopCat.of (Path (Path.refl (stagePoint 1 W)) (Path.refl (stagePoint 1 W))))
    (fun k => TopCat.of (Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)))
  point n := by
    cases n with
    | zero => exact Path.refl (Path.refl (stagePoint 1 W))
    | succ k => exact Path.refl (stagePoint (k + 1) W)
  structureMap n := by
    cases n with
    | zero => exact ContinuousMap.id _
    | succ k => exact rowLoopStageStructure k W
  map_point n := by
    cases n with
    | zero => rfl
    | succ k => exact rowLoopStageStructure_point k W

/-- The original row cylinders form an actual whole-spectrum map to the distinguished-row target.
-/
def rowStabilizationMap (W : WideSubcategory preservesZero.{u}) :
    prespectrum W ⟶ rowLoopPrespectrum W where
  map n := Nat.casesOn n
    (basedLoopMap (stageLoopMap 0 W) (stageLoopMap_point 0 W))
    (fun k => stageLoopMap k W)
  map_point n := by
    cases n with
    | zero => exact basedLoopMap_refl _ _
    | succ k => exact stageLoopMap_point k W
  comm n x := by
    cases n with
    | zero => rfl
    | succ k =>
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      exact (stageLoopMap_rowSwap k W x s r).symm

/-- The unchanged positive comparison level is the genuine original row cylinder. -/
theorem rowStabilizationMap_succ (W : WideSubcategory preservesZero.{u}) (k : ℕ) :
    (rowStabilizationMap W).map (k + 1) = stageLoopMap k W := rfl

/-- Degree zero is the actual loop extension, retaining the input-loop and new row times. -/
theorem rowStabilizationMap_zero (W : WideSubcategory preservesZero.{u})
    (γ : Path (stagePoint 0 W) (stagePoint 0 W)) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((rowStabilizationMap W).map 0 γ) r) s =
        stageLoopMap 0 W (γ r) s := rfl

end CategoryTheory.Waldhausen.IteratedS
