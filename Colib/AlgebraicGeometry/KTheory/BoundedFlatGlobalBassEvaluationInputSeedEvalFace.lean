/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalRails
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalNullNative
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedWords

/-! The full original raw seed on an independently moving evaluation input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v w
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalFace
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem trans_value {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] {p q k : C(A, B)}
    (P : p.Homotopy q) (Q : q.Homotopy k)
    {E F : LoopPrespectrum.{u}} {f h j : E ⟶ F}
    (H : Homotopy f h) (K : Homotopy h j) (n : ℕ) (x : E.space n)
    (ev : B → F.space n) (a : A)
    (hP : ∀ t, ev (P (t, a)) = H.level n (t, x))
    (hQ : ∀ t, ev (Q (t, a)) = K.level n (t, x)) (s : I) :
    ev ((P.trans Q) (s, a)) = (H.trans K).level n (s, x) := by
  change ev ((P.trans Q) (s, a)) =
    ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hP _
  · exact hQ _

/-- The actual unit product runs between the complete original null source rails. -/
def unitSwap : (InputSeedEvalNull.source g false).Homotopy
    (InputSeedEvalNull.source g true) where
  toFun z := InputSeedEvalRails.unit g (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := InputSeedEvalRails.unit_zero g r
  map_one_left r := InputSeedEvalRails.unit_one g r

/-- The original inverse-null/(unit/null) word, with precisely its original nested cuts. -/
def wordSwap : (ContinuousMap.const I (InputSeedInputNull.tip g false)).Homotopy
    (ContinuousMap.const I (InputSeedInputNull.tip g true)) :=
  (InputSeedEvalNull.nullSwap g false).symm.trans
    ((unitSwap g).trans (InputSeedEvalNull.nullSwap g true))

/-- The complete two-time fifth face lives in the actual mixed seed carrier. -/
def parameter : C(I × I, Carrier g) :=
  ⟨fun z ↦ wordSwap g (z.2, z.1), by fun_prop⟩

/-- The fixed input retains its exact inverse-null/unit/null path word. -/
def word (r : I) :=
  (InputSeedEvalNull.path g false r).symm.trans
    ((InputSeedEvalRails.unitPath g r).trans (InputSeedEvalNull.path g true r))

/-- The whole face recovers the specified complete word at every evaluation input. -/
theorem parameter_word (r s : I) : parameter g (r, s) = word g r s := by
  rfl

/-- The entire source edge is the original raw seed word at the initial evaluation. -/
theorem source (s : I) : parameter g (0, s) = word g 0 s := parameter_word g 0 s

/-- The entire target edge is the original raw seed word at the terminal evaluation. -/
theorem target (s : I) : parameter g (1, s) = word g 1 s := parameter_word g 1 s

/-- The ordinary tip remains fixed along the full evaluation time. -/
theorem zero (r : I) : parameter g (r, 0) = InputSeedInputNull.tip g false :=
  (wordSwap g).apply_zero r

/-- The separately shifted tip remains fixed along the full evaluation time. -/
theorem one (r : I) : parameter g (r, 1) = InputSeedInputNull.tip g true :=
  (wordSwap g).apply_one r

/-- The middle product is the original unit at the independently moving native input. -/
theorem unit_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (unitSwap g (s, r)) x =
      (((GlobalRawBass.unitHomotopy X).postcomp
        (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).level n
        (s, (evaluationComparison g).level n (r, x))) := by
  refine (CutOpenCarrier.nativeEval_laurentInclusion
    (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) (shifted g) n
    (InputSeedEvaluationProduct.parameter g (r, s)) x).trans ?_
  exact congrArg ((mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n)
    ((pointwisePrespectrumFamily_parameter (laurentRef g)
      (InputSeedEvaluationProduct.nodes g) n
      (InputSeedEvaluationProduct.scalar.{u} (r, s)) x).trans
        (InputSeedEvaluationProduct.native g n r s x))

/-- The complete positive-cone seed is recovered at all independent evaluation and loop times. -/
theorem positive_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (parameter g (r, s)) x =
      Path.toContinuousMap ((GlobalRawBass.InputIdentityPositive.seed X).map n
        ((evaluationComparison g).level n (r, x))) s := by
  change InputSeedInputNull.nativeEval g n
    (((InputSeedEvalNull.nullSwap g false).symm.trans
      ((unitSwap g).trans (InputSeedEvalNull.nullSwap g true))) (s, r)) x =
    ((((GlobalRawBass.unitHomotopy X).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).conjugateToZero
        (GlobalRawBass.InputIdentityPositive.sourceNull X)).level n
          (s, (evaluationComparison g).level n (r, x)))
  unfold Homotopy.conjugateToZero
  let ev := fun z : Carrier g ↦ InputSeedInputNull.nativeEval g n z x
  exact trans_value (InputSeedEvalNull.nullSwap g false).symm
    ((unitSwap g).trans (InputSeedEvalNull.nullSwap g true))
    (GlobalRawBass.InputIdentityPositive.sourceNull X).symm
    (((GlobalRawBass.unitHomotopy X).postcomp
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).trans
        (GlobalRawBass.InputIdentityPositive.sourceNull X)) n
    ((evaluationComparison g).level n (r, x)) ev r
    (fun t ↦ InputSeedEvalNull.native g false n r (unitInterval.symm t) x)
    (fun t ↦ trans_value (unitSwap g) (InputSeedEvalNull.nullSwap g true)
      ((GlobalRawBass.unitHomotopy X).postcomp
        (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)))
      (GlobalRawBass.InputIdentityPositive.sourceNull X) n
      ((evaluationComparison g).level n (r, x)) ev r
      (fun v ↦ unit_native g n r v x)
      (fun v ↦ InputSeedEvalNull.native g true n r v x) t) s

/-- The actual fifth prescribed homotopy keeps every original full-cone and loop coordinate. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.evaluationSecond g).level n (r, x)) s := by
  rw [positive_native, InputSeedWords.evaluationSecond_apply]
  have h := congrArg
    (fun f ↦ Path.toContinuousMap (f.map n ((evaluationComparison g).level n (r, x))) s)
    (GlobalRawBass.InputIdentityPositive.seed_factor X)
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalFace
