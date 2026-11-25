/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterPaths
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanTargetColumn
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputTargetFace
public import Colib.Topology.Path.ScalarPathCells

/-!
# The complete actual-composite target seam of the input-span parameter

The original evaluation column and polynomial square are recovered from their entire top
chart. The five resulting leaves agree with the original raw pasted target word, including
both normalization halves and all nested concatenation coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterTarget
open GlobalSectionChangeIndex InputSpanParameterWord
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The exact first half of either original chart is its complete evaluation column. -/
theorem chart_first (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (s : unitInterval) :
    chartSwap g k hk (Path.CarrierHalfPaths.lower s, 1) =
      InputRawChartProductNodes.parameter g k hk (s, 1) :=
  (chart_initial g k hk s).trans (InputSpanTargetColumn.column_parameter g k hk s)

/-- The complete five-leaf actual target is the original three-sheet raw pasted boundary. -/
theorem actual_top (s : unitInterval) :
    actualTop g s = InputRawPastedParameter.parameter g (1, s) := by
  rcases Path.CarrierHalfPaths.three_cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · unfold actualTop
    rw [Path.CarrierHalfPaths.path_lower, InputRawPastedParameter.parameter_lower]
    exact chart_first g plus GlobalRawBass.plus_projection t
  · unfold actualTop
    rw [Path.CarrierHalfPaths.path_upper, Path.CarrierHalfPaths.path_lower,
      InputRawPastedParameter.parameter_middle]
    exact middle_top g t
  · unfold actualTop
    rw [Path.CarrierHalfPaths.path_upper, Path.CarrierHalfPaths.path_upper,
      InputRawPastedParameter.parameter_upper]
    exact chart_first g minus GlobalRawBass.minus_projection (unitInterval.symm t)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterTarget

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSeams
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire target face ends at the original actual-composite input-span boundary. -/
theorem target (s : unitInterval) :
    InputTargetFace.parameter g (1, s) = InputSpanParameterWord.parameter g (1, s) := by
  rw [InputSpanParameterWord.parameter_one]
  exact (Topology.ScalarRectangle.concatFirst_one
    (InputMixedDesc.postSquareParameter g) (InputRawPastedParameter.parameter g)
    (InputRawPastedSeam.seam g) s).trans (InputSpanParameterTarget.actual_top g s).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterSeams
