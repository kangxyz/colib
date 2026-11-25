/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluation
public import Colib.Topology.Prespectrum.ConeSquareMapStrictPrecomposition

/-!
# Strict source maps in global Bass evaluation

The strict section diagram acts by its literal commuting square, both on the polynomial
double cylinder and on the comparison cone. Precomposition of the original geometric
evaluation by this square map does not insert a pause into the cone track.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation

namespace InputSpan

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The literal strict input map of the original global section square. -/
def sectionSpanMap : StrictSquare.span (sectionSquare Y) ⟶
    StrictSquare.span (sectionSquare X) :=
  StrictSquare.spanMap (sectionDiagram.mapArrow.mapArrow.map (squareFunctor.map g.op))

/-- The strict input retains the original cylinder coordinate literally. -/
theorem sectionSpanMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (sectionDiagram.obj (op Y)).space n) :
    (sectionSpanMap g).map n
      (HomotopyPushout.cylinder (sectionMap (projection.app Y))
        (sectionMap (projection.app Y)) n (s, x)) =
      HomotopyPushout.cylinder (sectionMap (projection.app X))
        (sectionMap (projection.app X)) n (s, (sectionMap g).map n x) := rfl

/-- The original strict comparison is natural for the actual diagram restriction. -/
theorem strict_comparison :
    sectionSpanMap g ≫ StrictSquare.comparison (sectionSquare X) =
      StrictSquare.comparison (sectionSquare Y) ≫ sectionMap (laurent.map g) :=
  StrictSquare.comparison_naturality
    (sectionDiagram.mapArrow.mapArrow.map (squareFunctor.map g.op))

end InputSpan

/-- Every height of the original strict comparison cylinder is the same Laurent restriction. -/
theorem strict_comparison_cylinder (X : Scheme.{u}) (n : ℕ) (s : unitInterval)
    (x : (sectionDiagram.obj (op X)).space n) :
    (StrictSquare.comparison (sectionSquare X)).map n
      (HomotopyPushout.cylinder (sectionMap (projection.app X))
        (sectionMap (projection.app X)) n (s, x)) =
      (sectionMap (GlobalRawBass.laurentProjection.app X)).map n x := by
  change (sectionMap (projection.app X) ≫ sectionMap (plus.app X)).map n x = _
  rw [← sectionMap_comp, GlobalRawBass.plus_projection]

namespace InputConeSource

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original strict square induces its actual commuting comparison-arrow square. -/
def comparisonArrow :
    Arrow.mk (StrictSquare.comparison (sectionSquare Y)) ⟶
      Arrow.mk (StrictSquare.comparison (sectionSquare X)) :=
  strictSquareComparisonFunctor.map
    (sectionDiagram.mapArrow.mapArrow.map (squareFunctor.map g.op))

/-- The strict input is the original cone functor on the actual comparison arrow. -/
def strictConeMap : mappingCone (StrictSquare.comparison (sectionSquare Y)) ⟶
    mappingCone (StrictSquare.comparison (sectionSquare X)) :=
  mappingConeMap (comparisonArrow g)

/-- The direct cone track is the actual evaluation track after literal strict precomposition. -/
def strictPrecompTrack :=
  mappingConeSquareStrictPrecompTrack
    (StrictSquare.comparison (sectionSquare Y)) (StrictSquare.comparison (sectionSquare X))
    (GlobalRawBass.comparison X) (comparisonArrow g) (spanEvaluation X)
    (evaluation (laurent.obj X)) (comparisonHomotopy X)

/-- The direct cone map retains the original half clock of the strictly precomposed evaluation. -/
def directConeMap :=
  mappingConeSquareMap (StrictSquare.comparison (sectionSquare Y)) (GlobalRawBass.comparison X)
    (InputSpan.sectionSpanMap g ≫ spanEvaluation X)
    (sectionMap (laurent.map g) ≫ evaluation (laurent.obj X)) (strictPrecompTrack g)

/-- Strict precomposition retains every point of the original geometric square-cone map. -/
theorem strict_comp_evaluation : strictConeMap g ≫ coneEvaluation X = directConeMap g :=
  mappingConeMap_comp_squareMap
    (StrictSquare.comparison (sectionSquare Y)) (StrictSquare.comparison (sectionSquare X))
    (GlobalRawBass.comparison X) (comparisonArrow g) (spanEvaluation X)
    (evaluation (laurent.obj X)) (comparisonHomotopy X)

/-- Original parameter looping preserves the literal whole-map identification. -/
theorem strict_loop_comp_evaluation :
    parameterLoopingMap (strictConeMap g) ≫ stepEvaluation X =
      parameterLoopingMap (directConeMap g) :=
  (parameterLoopingFunctor.map_comp (strictConeMap g) (coneEvaluation X)).symm.trans
    (congrArg parameterLoopingMap (strict_comp_evaluation g))

/-- The existing global strict Bass diagram acts by this very looped strict cone map. -/
theorem strict_input_eq :
    (((KTheory.Bass.strictDiagramFunctor squareFunctor).obj sectionDiagram).map g.op) =
      parameterLoopingMap (strictConeMap g) := rfl

end InputConeSource
end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
