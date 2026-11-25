/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCommutingSimplex
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftCommonPrefix
public import Colib.KTheory.Waldhausen.Iterated.ScalarRouteExtraction

/-!
# The exact finite parameter of the original moving evaluation square

The two unchanged composition faces share their actual total evaluation edge. The same
common-prefix cancellation word and three-side collapse produce the complete native square.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCommutingParameter
open InputCommutingSimplex

/-- The selected scalar square has exactly the four unpaused original boundary paths. -/
def parameterSquare : ParameterSquare (edge (k := 7) 0 6)
    ((edge 3 4).trans (((edge 1 2).trans (edge 2 4)).symm.trans ((edge 1 5).trans (edge 5 7))))
    (edge 0 3) (edge 6 7) :=
  SimplexParameters.commonPrefixSquare
    (compositionParameter firstFace) (compositionParameter secondFace)

/-- The complete original cancellation parameter, including its three-side collapse. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 8)) :=
  parameterSquare.parameter

/-- The original X evaluation track, with no inserted pause. -/
theorem parameter_zero (s : unitInterval) : parameter (0, s) = edge (k := 7) 0 6 s :=
  parameterSquare.at_zero s

/-- The Y evaluation followed by both original split composition routes. -/
theorem parameter_one (s : unitInterval) :
    parameter (1, s) =
      ((edge (k := 7) 3 4).trans
        (((edge 1 2).trans (edge 2 4)).symm.trans ((edge 1 5).trans (edge 5 7)))) s :=
  parameterSquare.at_one s

/-- The polynomial or chart evaluation edge retains its entire original clock. -/
theorem parameter_left (r : unitInterval) : parameter (r, 0) = edge (k := 7) 0 3 r :=
  parameterSquare.left r

/-- The input evaluation edge retains its entire original clock. -/
theorem parameter_right (r : unitInterval) : parameter (r, 1) = edge (k := 7) 6 7 r :=
  parameterSquare.right r

variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
  (h : p ≫ v = q ≫ w)

/-- The whole finite scalar square realizes the actual four-leg evaluation square. -/
theorem native : SquareLift (simplex p v q w h) parameterSquare
    (InputCommutingSquare.square p v q w h) := by
  let S := simplex p v q w h
  have hJ := first_comparison_native p v q w h
  have hK := second_comparison_native p v q w h
  have hC := PathLift.trans_left S (HomotopyLift.source S hJ)
  have hD := PathLift.trans_right S (HomotopyLift.source S hJ)
  have hF := PathLift.trans_right S (HomotopyLift.source S hK)
  have hL := PathLift.trans_left S (HomotopyLift.target S hJ)
  have hP := PathLift.trans_right S (HomotopyLift.target S hJ)
  have hT := PathLift.trans_left S (HomotopyLift.target S hK)
  have hM := PathLift.trans_right S (HomotopyLift.target S hK)
  have hl := HomotopyLift.commonPrefixSquare S hC hD hF hL hP hT hM hJ hK
  intro n r s x
  exact hl n r s x

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCommutingParameter
