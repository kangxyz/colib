/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterEval

/-!
# The full original split-normalization family at moving evaluation input

The accepted full prism family is composed with the original terminal-face coordinate map.
Its complete native family equality precedes any pointwise specialization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace Topology
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterPrism
open GlobalSectionChangeIndex SmallWaldhausenCategory
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem moving_cut (n : ℕ) :
    (InputNormalizationPrism.movingParameter g n).comp (inputCut (Y := Y) n) =
      (⟨fun z ↦ (1, rawInput g n z), by fun_prop⟩ : C(_, _)) := rfl

/-- The whole two-parameter native family is the original composition track at moving input. -/
theorem whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n =
      ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
        (k.app X) (projection.app X)).level n).comp
        (rawInput g n) :=
  (restricted_whole g k hk n).trans
    ((congrArg (fun A ↦ A.comp (inputCut (Y := Y) n))
      (InputChartReference.prism_whole_native g k hk n)).trans
      ((ContinuousMap.comp_assoc
        (((boundedAboveFlatPerfectNormalizedCompTrackComparison
          (k.app X) (projection.app X)).level n).toContinuousMap)
        (InputNormalizationPrism.movingParameter g n) (inputCut (Y := Y) n)).trans
        ((congrArg (fun A ↦
          ((boundedAboveFlatPerfectNormalizedCompTrackComparison
            (k.app X) (projection.app X)).level n).toContinuousMap.comp A) (moving_cut g n)).trans
          (comparison_one_whole (k.app X) (projection.app X) n (rawInput g n)))))

/-- Every original split-path point is retained at the independent evaluation input. -/
theorem native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n ((r, s), x) =
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (k.app X) (projection.app X)).level n
      (s, (evaluationComparison g).level n (r, x)) :=
  DFunLike.congr_fun (whole_native g k hk n) ((r, s), x)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterPrism
