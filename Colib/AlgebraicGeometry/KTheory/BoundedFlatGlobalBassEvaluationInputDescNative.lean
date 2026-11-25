/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartNative
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputStrictPaste

/-!
# The whole selected global evaluation descent surface in one original diagram

The actual two-chart pasting is lifted through the original scalar constant-source cancellation
word. This identifies every point of the already selected descPasting, including all binary
normalization, reflexive insertion, and cancellation seams. It does not fill the mixed input
cone cube, whose prescribed faces and nested cone-height clocks remain separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSimplex
variable (X : Scheme.{u})

/-- The literal scalar counterpart of the selected original strict-source overlap pasting. -/
def descParameter :=
  InputStrictPaste.parameter (InputParameter.chart plusFace) (InputParameter.chart minusFace)

/-- The whole original two-chart overlap is evaluated in the genuine common Model simplex. -/
theorem boundary_native : HomotopyLift (simplex X) descParameter (boundary X) := by
  have lp := plus_native X
  have lm := minus_native X
  have lLp := PathLift.trans_left _ (HomotopyLift.source _ lp)
  have lPp := PathLift.trans_right _ (HomotopyLift.source _ lp)
  have lT := PathLift.trans_left _ (HomotopyLift.target _ lp)
  have lKp := PathLift.trans_right _ (HomotopyLift.target _ lp)
  have lLm := PathLift.trans_left _ (HomotopyLift.source _ lm)
  have lPm := PathLift.trans_right _ (HomotopyLift.source _ lm)
  have lKm := PathLift.trans_right _ (HomotopyLift.target _ lm)
  exact InputStrictPaste.native (simplex X) lT lLp lPp lKp lLm lPm lKm lp lm

/-- Endpoint transports preserve the entire already chosen global evaluation descent surface. -/
theorem desc_native : HomotopyLift (simplex X) descParameter (descPasting X) := by
  intro n r s x
  exact boundary_native X n r s x

/-- The literal selected surface keeps its original native prespectrum point. -/
theorem desc_parameter_point (n : ℕ) (r s : unitInterval) :
    prespectrumSimplexFamily (simplex X) n
      (descParameter (r, s),
        (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).point n) =
      (prespectrum (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace))).point n :=
  prespectrumSimplexFamily_point _ _ _

/-- The entire two-dimensional face is independent of the original spectrum-structure time. -/
theorem desc_parameter_structure (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex X) (n + 1)
      (descParameter (r, s),
        (prespectrum
          (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).structureMap n x t) =
      (prespectrum (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace))).structureMap n
        (prespectrumSimplexFamily (simplex X) n (descParameter (r, s), x)) t :=
  prespectrumSimplexFamily_structure _ _ _ _ _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSimplex
