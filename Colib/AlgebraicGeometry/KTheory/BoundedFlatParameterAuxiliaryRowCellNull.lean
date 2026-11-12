/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowNullLegs
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedBoundary
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentBoundary

/-! # Original auxiliary null time slices preserve the independent first-row cells

The original transformation null commutes with the computed row interchange and the actual
Laurent action. The previously proved independent-cell comparison therefore gives the whole
cell square, retaining the null time independently of the cell time.
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
open GeometricSeedCospan NaturalTrack ModelDiagramRowInterchange
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The actual original finite null at one time, as a complete natural transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowCellNull.lean:32"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullNullStageMap (i : ℕ) (r : unitInterval) :=
  diagramHomotopyAt
    (η := (strictDiagramIterate squareFunctor i).map (firstMap f T) ≫
      (strictDiagramIterate squareFunctor i).map (secondMap f T))
    (θ := diagramZeroMap
      ((strictDiagramIterate squareFunctor i).obj (fiber f T ⋙ prespectrumFunctor))
      ((strictDiagramIterate squareFunctor i).obj (openModel f T ⋙ prespectrumFunctor)))
    (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy
    (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality r

/-- The actual finite null time slice preserves the original computed row interchange. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowCellNull.lean:43"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNullStageMap_row (i : ℕ) (r : unitInterval) (X : Scheme.{u}ᵒᵖ) (k : ℕ)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space (k + 3)) :
    stage squareFunctor (openModel f T) i X k
        (((fullNullStageMap f T i r).app X).map (k + 3) x) =
      ((fullNullStageMap f T i r).app X).map (k + 3)
        (stage squareFunctor (fiber f T) i X k x) :=
  fullNull_stage_row f T i X k r x

/-- The actual finite null time slice preserves the whole Laurent action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowCellNull.lean:53"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNullStageMap_equivariant (i : ℕ) (r : unitInterval) :
    Equivariant (SchemeNaturalSeed.stageTrack (fiberAction f T) i)
      (SchemeNaturalSeed.stageTrack (openAction f T) i) (fullNullStageMap f T i r) := by
  unfold fullNullStageMap
  rw [strictDiagramIterateNull_timeSlice]
  exact (timeSlice_equivariant f T r).stages (L := laurent.op) (c := coefficient)
    squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i

/-- The same null time induces the genuine row map on every original finite object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowCellNull.lean:66"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullNullStageRowMap (i : ℕ) (r : unitInterval) (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.map (stage squareFunctor (fiber f T) i X)
    (stage squareFunctor (openModel f T) i X)
    (stage_point squareFunctor (fiber f T) i X)
    (stage_point squareFunctor (openModel f T) i X)
    ((fullNullStageMap f T i r).app X) (fullNullStageMap_row f T i r X)

/-- The original comparison commutes with the actual null-induced row map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowCellNull.lean:74"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNullStageComparison_square (i : ℕ) (r : unitInterval) (X : Scheme.{u}ᵒᵖ) :
    (fullNullStageMap f T i r).app X ≫
        (DiagramRowRefinement.comparison _ (stage squareFunctor (openModel f T) i)
          (stage_point squareFunctor (openModel f T) i)
          (stage_naturality squareFunctor (openModel f T) i)
          (stage_structure squareFunctor (openModel f T) i)).app X =
      (DiagramRowRefinement.comparison _ (stage squareFunctor (fiber f T) i)
          (stage_point squareFunctor (fiber f T) i)
          (stage_naturality squareFunctor (fiber f T) i)
          (stage_structure squareFunctor (fiber f T) i)).app X ≫
        fullNullStageRowMap f T i r X :=
  RowRefinement.comparison_naturality _ _ _ _ _ (fullNullStageMap_row f T i r X)
    (stage_structure squareFunctor (fiber f T) i X)
    (stage_structure squareFunctor (openModel f T) i X)

/-- Null time and independent first-row cell time are retained in the full map square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowCellNull.lean:90"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_cell_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r t : unitInterval) :
    (SchemeModelRowSeed.cell (fiber f T) (supportedUnit (unionOpen f T).ι)
        (supportedUnit_naturality (unionOpen f T).ι) i X).at t ≫
        fullNullStageRowMap f T i r (laurent.op.obj X) =
      (fullNullStageMap f T i r).app X ≫
        (SchemeModelRowSeed.cell (openModel f T) (supportedUnit (inverseOpen f T).ι)
          (supportedUnit_naturality (inverseOpen f T).ι) i X).at t := by
  rw [SchemeModelRowSeed.cell_eq, SchemeModelRowSeed.cell_eq]
  change (((SchemeNaturalSeed.stageTrack (fiberAction f T) i).homotopy X).at t ≫ _) ≫ _ =
    _ ≫ (((SchemeNaturalSeed.stageTrack (openAction f T) i).homotopy X).at t ≫ _)
  rw [Category.assoc, ← fullNullStageComparison_square,
    ← Category.assoc, ← fullNullStageMap_equivariant f T i r X t, Category.assoc]

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
