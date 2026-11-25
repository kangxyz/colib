/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawChartProductNodes
public import Colib.Topology.Path.ScalarRectangleConcatenation

/-!
# The actual three-piece raw input surface on the evaluated span cylinder

The positive moving-input square, entire original raw descent surface, and reversed inverse
moving-input square glue on their proved complete common-reference edges. Their original
height intervals are the first half, middle quarter, and final quarter respectively.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawPastedParameter
open GlobalSectionChangeIndex Path.CarrierHalfPaths
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The positive sheet keeps square time first and moving projection-evaluation time second. -/
def plusSheet :=
  ScalarRectangle.swap
    (InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection)

/-- The inverse sheet reverses only the original projection-evaluation height coordinate. -/
def minusSheet :=
  (InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection).comp
    (⟨fun z => (unitInterval.symm z.2, z.1), by fun_prop⟩ :
      C(unitInterval × unitInterval, unitInterval × unitInterval))

/-- The complete shared inverse edge is the actual terminal product row. -/
theorem minus_seam (r : unitInterval) :
    InputRawDesc.parameter g (r, 1) = minusSheet g (r, 0) := by
  change InputRawDesc.parameter g (r, 1) =
    InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection
      (unitInterval.symm 0, r)
  rw [unitInterval.symm_zero]
  exact (InputRawChartProductNodes.minus_attachment g r).symm

/-- The whole original raw descent is followed by the separate reversed inverse product. -/
def tailParameter :=
  ScalarRectangle.concatSecond (InputRawDesc.parameter g) (minusSheet g) (minus_seam g)

/-- The complete positive product row is exactly the original raw descent source edge. -/
theorem plus_seam (r : unitInterval) : plusSheet g (r, 1) = tailParameter g (r, 0) :=
  (InputRawChartProductNodes.plus_attachment g r).trans
    (ScalarRectangle.concatSecond_zero (InputRawDesc.parameter g) (minusSheet g)
      (minus_seam g) r).symm

/-- The actual three surfaces retain the selected right-associated half-clock concatenation. -/
def parameter :=
  ScalarRectangle.concatSecond (plusSheet g) (tailParameter g) (plus_seam g)

/-- Every point of the first half is the original positive moving-input product square. -/
theorem parameter_lower (r s : unitInterval) :
    parameter g (r, lower s) =
      InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection (s, r) :=
  ScalarRectangle.concatSecond_lower (plusSheet g) (tailParameter g) (plus_seam g) r s

/-- Every point of the middle quarter is the entire original raw descent surface. -/
theorem parameter_middle (r s : unitInterval) :
    parameter g (r, upper (lower s)) = InputRawDesc.parameter g (r, s) :=
  (ScalarRectangle.concatSecond_upper
    (plusSheet g) (tailParameter g) (plus_seam g) r (lower s)).trans
    (ScalarRectangle.concatSecond_lower
      (InputRawDesc.parameter g) (minusSheet g) (minus_seam g) r s)

/-- Every point of the final quarter keeps the original reversed inverse evaluation height. -/
theorem parameter_upper (r s : unitInterval) :
    parameter g (r, upper (upper s)) =
      InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection
        (unitInterval.symm s, r) :=
  (ScalarRectangle.concatSecond_upper
    (plusSheet g) (tailParameter g) (plus_seam g) r (upper s)).trans
    (ScalarRectangle.concatSecond_upper
      (InputRawDesc.parameter g) (minusSheet g) (minus_seam g) r s)

/-- The original positive strict-input row is the whole lower boundary. -/
theorem parameter_left (r : unitInterval) :
    parameter g (r, 0) =
      InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection (0, r) :=
  ScalarRectangle.concatSecond_zero (plusSheet g) (tailParameter g) (plus_seam g) r

/-- The distinct inverse strict-input row is the whole upper boundary. -/
theorem parameter_right (r : unitInterval) :
    parameter g (r, 1) =
      InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection (0, r) := by
  refine (ScalarRectangle.concatSecond_one
    (plusSheet g) (tailParameter g) (plus_seam g) r).trans ?_
  refine (ScalarRectangle.concatSecond_one
    (InputRawDesc.parameter g) (minusSheet g) (minus_seam g) r).trans ?_
  change InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection
    (unitInterval.symm 1, r) = _
  rw [unitInterval.symm_one]

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawPastedParameter
