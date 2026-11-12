/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryRowNullEndpoint
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryTwistedNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNullComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull
public import Colib.KTheory.Bass.ModelRowBackwardNaturality

/-! # The prescribed auxiliary null through the original backward row legs

The actual successor casts and row comparisons retain the same original null time.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open GeometricSeedCospan ModelRowZigzagSequentialization
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original whole cone time slice is the cone map of the original finite null slice. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullBackward.lean:30"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullConeNull_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (fullConeNull f T i X).at r =
      (ConeTrack.map squareFunctor ((strictDiagramIterate squareFunctor i).map
        (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
          (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
            (openModel f T ⋙ prespectrumFunctor))
          (fullNull f T).homotopy (fullNull f T).naturality r))).app X := by
  rw [fullConeNull, StrictSquare.MapHomotopy.cone_at, (diagramSquareMapHomotopy_at
      (hH := (strictDiagramIterateNull squareFunctor (fullNull f T) i).naturality)),
    strictDiagramIterateNull_timeSlice]
  rfl

/-- The actual successor identification retains every time of the original finite null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullBackward.lean:43"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullNull_successor_cone_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    ((strictDiagramIterateNull squareFunctor (fullNull f T) (i + 1)).homotopy X).at r ≫
        eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i (openModel f T) X) =
      eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i (fiber f T) X) ≫
        parameterLoopingMap ((fullConeNull f T i X).at r) := by
  rw [strictDiagramIterateNull_at, fullConeNull_at]
  have h := (eqToHom (strictDiagramIterate_succ_right squareFunctor i)).naturality
    (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
      (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
        (openModel f T ⋙ prespectrumFunctor))
      (fullNull f T).homotopy (fullNull f T).naturality r)
  have hx := congrArg (fun a => a.app X) h
  simp only [NatTrans.comp_app, eqToHom_app, Functor.comp_map] at hx
  exact hx

/-- The actual proper target homotopy is the original refined row homotopy, parameter-looped. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullBackward.lean:59"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def fullTargetNull (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (fullRowNull f T i X).parameterLooping

/-- Every original backward leg preserves the entire auxiliary null, with its time unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryRowNullBackward.lean:63"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem fullTargetNull_backward_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    ((strictDiagramIterateNull squareFunctor (fullNull f T) (i + 1)).homotopy X).at r ≫
        backward squareFunctor (openModel f T) X i =
      backward squareFunctor (fiber f T) X i ≫ (fullTargetNull f T i X).at r := by
  rw [backward_eq, backward_eq]
  change _ ≫ (eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i
      (openModel f T) X) ≫ parameterLoopingMap
        (ModelDiagramRowRefinement.comparison squareFunctor i (openModel f T) X)) =
    (eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i (fiber f T) X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison squareFunctor i (fiber f T) X)) ≫ _
  rw [← Category.assoc, fullNull_successor_cone_at, Category.assoc, Category.assoc]
  have h := congrArg parameterLoopingFunctor.map (fullRowNull_comparison_at f T i X r)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact congrArg (fun k =>
    eqToHom (ModelDiagramSuspension.successor_obj squareFunctor i (fiber f T) X) ≫ k) h

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
