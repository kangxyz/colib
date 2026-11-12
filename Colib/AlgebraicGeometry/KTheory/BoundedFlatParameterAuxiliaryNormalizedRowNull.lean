/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowCellNull
public import Colib.KTheory.Bass.DiagramRowNormalizedBoundaryNaturality

/-! # The original auxiliary null commutes with the whole boundary normalization prism

The two independent times are the prescribed localization-null time and the normalization
prism time. Both are retained through the actual finite cone, row carrier and outer loop.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open GeometricSeedCospan ModelDiagramRowInterchange
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original moving cone at each time is exactly the cone map of that time slice. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowN\
    ull.lean:31"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullConeNull_at_stageMap (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (fullConeNull f T i X).at r =
      (ConeTrack.map squareFunctor (fullNullStageMap f T i r)).app X := by
  rw [fullConeNull_at, fullNullStageMap, strictDiagramIterateNull_timeSlice]

/-- The genuine target null at each time is the actual outer-loop cone row map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowN\
    ull.lean:37"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullTargetNull_at_coneRowMap (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (fullTargetNull f T i X).at r = parameterLoopingMap
      (DiagramRowSeed.coneRowMap squareFunctor
        (stage squareFunctor (fiber f T) i) (stage_point squareFunctor (fiber f T) i)
        (stage_naturality squareFunctor (fiber f T) i)
        (stage squareFunctor (openModel f T) i) (stage_point squareFunctor (openModel f T) i)
        (stage_naturality squareFunctor (openModel f T) i)
        (fullNullStageMap f T i r) (fullNullStageMap_row f T i r) X) := by
  rw [fullTargetNull, Homotopy.parameterLooping_at, fullRowNull, refineWholeRowHomotopy_at]
  congr 1
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    change Path (Path.refl ((ModelDiagramRowRefinement.source
      squareFunctor i (fiber f T) X).point 2)) (Path.refl
        ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point 2)) at x
    apply Path.ext
    funext s
    apply Path.ext
    funext a
    exact congrArg (fun g => g.map 2 (x s a)) (fullConeNull_at_stageMap f T i X r)
  | succ k =>
    change Path ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2))
      ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point (k + 2)) at x
    apply Path.ext
    funext s
    exact congrArg (fun g => g.map (k + 2) (x s)) (fullConeNull_at_stageMap f T i X r)

/-- The entire normalized-boundary prism preserves the original auxiliary null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowN\
    ull.lean:69"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_normalizedBoundaryHomotopy (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (r s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space n) :
    (fullTargetNull f T i X).level n
        (r, (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (fiber f T)
          (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
          i X).level n (s, x)) =
      (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (openModel f T)
          (supportedUnit (inverseOpen f T).ι) (supportedUnit_naturality (inverseOpen f T).ι)
          i X).level n
        (s, ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level n
          (r, x)) := by
  change ((fullTargetNull f T i X).at r).map n _ = _
  rw [fullTargetNull_at_coneRowMap]
  exact DiagramRowSeed.normalizedBoundaryHomotopy_naturality_apply squareFunctor
    (stage squareFunctor (fiber f T) i) (stage_point squareFunctor (fiber f T) i)
    (stage_naturality squareFunctor (fiber f T) i)
    (stage squareFunctor (openModel f T) i) (stage_point squareFunctor (openModel f T) i)
    (stage_naturality squareFunctor (openModel f T) i)
    (stage_structure squareFunctor (fiber f T) i)
    (stage_structure squareFunctor (openModel f T) i)
    (fullNullStageMap f T i r) (fullNullStageMap_row f T i r) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X
      (SchemeModelRowSeed.cell (fiber f T) (supportedUnit (unionOpen f T).ι)
        (supportedUnit_naturality (unionOpen f T).ι) i X))
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X
      (SchemeModelRowSeed.cell (openModel f T) (supportedUnit (inverseOpen f T).ι)
        (supportedUnit_naturality (inverseOpen f T).ι) i X))
    (fun k t y => congrArg (fun g => g.map k y) (fullNull_cell_at f T i X r t)) n s x

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
