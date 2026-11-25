/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalNullParam
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNullCells

/-! Native recovery of the original raw null at every independently moving evaluation input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalNull
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The whole polynomial edge retains the original evaluation time before raw projection. -/
theorem polynomial_native (n : ℕ) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily (polyRef g) n
      (InputSeedEvalBinary.polynomialParameter g r) x =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n
        ((evaluationComparison g).level n (r, x)) := by
  change pointwisePrespectrumFamily (polyRef g) n
    (CommonReferenceNerve.parameter _ _ (edge (k := 7) 6 7 r)) x = _
  rw [pointwisePrespectrumFamily_parameter]
  have h := InputCommutingParameter.native (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g) n r 1 x
  change prespectrumSimplexFamily _ n (InputCommutingParameter.parameter (r, 1), x) = _ at h
  rw [InputCommutingParameter.parameter_right] at h
  exact h.trans ((InputCommutingSquare.square (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g)).right n r x)

/-- Both independent times of the raw binary leg retain their actual positive-cone image. -/
theorem binary_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (binarySwap g e (s, r)) x =
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
        ((GlobalRawBass.plusHomotopy X).level n
          (s, (evaluationComparison g).level n (r, x))) := by
  change InputSeedInputNull.nativeEval g n
    (InputSeedInputNull.sheet g e (InputSeedEvalBinary.parameter g (r, s))) x = _
  rw [InputSeedInputNull.sheet_native, pointwisePrespectrumFamily_eq_compact]
  exact congrArg ((mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n)
    (InputSeedEvalBinary.native g n r s x)

/-- The actual cylinder preserves cone height, evaluation time and polynomial projection. -/
theorem cylinder_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (cylinderSwap g e (s, r)) x =
      (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X)).level n
        (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n
          ((evaluationComparison g).level n (r, x))) := by
  change InputSeedInputNull.nativeEval g n
    (InputSeedInputNull.cylinder g e (InputSeedEvalBinary.polynomialParameter g r, s)) x = _
  rw [InputSeedInputNull.cylinder_native, polynomial_native]
  rfl

/-- The original full raw null is recovered with its binary/cylinder half cut unchanged. -/
theorem native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (parameter g e (r, s)) x =
      (GlobalRawBass.InputIdentityPositive.sourceNull X).level n
        (s, (evaluationComparison g).level n (r, x)) := by
  change InputSeedInputNull.nativeEval g n
    (((binarySwap g e).trans (cylinderSwap g e)) (s, r)) x = _
  change InputSeedInputNull.nativeEval g n
    (((binarySwap g e).trans (cylinderSwap g e)) (s, r)) x =
      (((GlobalRawBass.plusHomotopy X).postcomp
        (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).levelHomotopy n).trans
        ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).levelHomotopy n)
          (s, (evaluationComparison g).level n (r, x))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact binary_native g e n r _ x
  · exact cylinder_native g e n r _ x

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalNull
