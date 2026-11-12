/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliarySupportNull
public import Colib.KTheory.Bass.DiagramRowNull
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan
public import Colib.KTheory.Bass.ModelDiagramRowInterchange
public import Colib.KTheory.Bass.ModelDiagramRowComparison
public import Colib.KTheory.Bass.ModelDiagramRowStability
public import Colib.KTheory.Waldhausen.Iterated.RowSwapTransformation

/-! # The original auxiliary supported null preserves every actual row interchange

The null is the prescribed reversed selected-zero transformation. No endpoint-only square
replaces its whole time parameter. Finite Bass stages use the original iterated null.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open ModelDiagramRowInterchange GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The actual weak zero transformation commutes with the original last-row transpose. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNull.lean:32"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_initial_row (X : Scheme.{u}ᵒᵖ) (k : ℕ) (r : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space (k + 3)) :
    initial (openModel f T) X k (((fullNull f T).homotopy X).level (k + 3) (r, x)) =
      ((fullNull f T).homotopy X).level (k + 3)
        (r, initial (fiber f T) X k x) := by
  rw [fullNull_level, fullNull_level]
  exact stageTransformationTopHomotopy_rowSwap k
    (zeroToFull f T X) (zeroToFull_weak f T X) (unitInterval.symm r) x

/-- Every original finite auxiliary null retains its exact time and computed stage row action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNull.lean:42"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_stage_row (i : ℕ) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (fiber f T ⋙ prespectrumFunctor)).obj X).space (k + 3)) :
    stage squareFunctor (openModel f T) i X k
        (((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level
          (k + 3) (r, x)) =
      ((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level
        (k + 3) (r, stage squareFunctor (fiber f T) i X k x) :=
  DiagramRowInterchange.iterate_null squareFunctor
    (F := fiber f T ⋙ prespectrumFunctor) (G := openModel f T ⋙ prespectrumFunctor)
    (initial (fiber f T)) (initial_point (fiber f T)) (initial_naturality (fiber f T))
    (initial (openModel f T)) (initial_point (openModel f T))
    (initial_naturality (openModel f T)) (fullNull f T) (fullNull_initial_row f T) i X k r x

/-- Every original moving cone preserves null time independently of both quotient heights. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNull.lean:57"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_cone_row (i : ℕ) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (r : unitInterval)
    (x : (ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).space (k + 3)) :
    cone squareFunctor i (openModel f T) X k
        ((diagramSquareMapHomotopy
          (η := (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (enlargement f T) prespectrumFunctor) ≫
            (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (restriction f T) prespectrumFunctor))
          (θ := diagramZeroMap
            ((strictDiagramIterate squareFunctor i).obj (fiber f T ⋙ prespectrumFunctor))
            ((strictDiagramIterate squareFunctor i).obj (openModel f T ⋙ prespectrumFunctor)))
          (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy
          (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality
          (squareFunctor.obj X)).cone.level (k + 3) (r, x)) =
      (diagramSquareMapHomotopy
          (η := (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (enlargement f T) prespectrumFunctor) ≫
            (strictDiagramIterate squareFunctor i).map
              (Functor.whiskerRight (restriction f T) prespectrumFunctor))
          (θ := diagramZeroMap
            ((strictDiagramIterate squareFunctor i).obj (fiber f T ⋙ prespectrumFunctor))
            ((strictDiagramIterate squareFunctor i).obj (openModel f T ⋙ prespectrumFunctor)))
        (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy
        (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality
        (squareFunctor.obj X)).cone.level (k + 3)
        (r, cone squareFunctor i (fiber f T) X k x) :=
  DiagramRowInterchange.cone_iterate_null squareFunctor
    (F := fiber f T ⋙ prespectrumFunctor) (G := openModel f T ⋙ prespectrumFunctor)
    (initial (fiber f T)) (initial_point (fiber f T)) (initial_naturality (fiber f T))
    (initial (openModel f T)) (initial_point (openModel f T))
    (initial_naturality (openModel f T)) (fullNull f T) (fullNull_initial_row f T) i X k r x

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
