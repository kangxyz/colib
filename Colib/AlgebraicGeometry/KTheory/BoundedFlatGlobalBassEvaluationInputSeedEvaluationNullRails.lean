/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNullChart

/-!
# Exact native values of the original objectwise null rails

The original chart surface supplies the whole positive and Laurent boundary words.
The actual cone interchange supplies the polynomial rail and both original cylinders.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
  Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullRails
open CommonReferenceNerve InputSeedEvaluationCarrier InputSeedEvaluationNullChart
variable (X : Scheme.{u}) (e : Bool)

private theorem carrier_path_apply {T : Type*} [TopologicalSpace T] {a b : T}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

/-- Every value of the original chart-source boundary word is retained. -/
theorem source_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n
      (((positiveMovement X e).trans (polynomialMovement X e)) s) x =
      (((InputPositiveNull.positiveMovement X).path n x).trans
        ((InputPositiveNull.polynomialMovement X).path n x)) s := by
  have h := positivePasting_native X e n 0 s x
  change CutOpenCarrier.nativeEval _ _ _ _ _ n ((positivePasting X e).toFun (0, s)) x = _ at h
  rw [(positivePasting X e).map_zero_left s] at h
  have he := h.trans (((InputPositiveNull.positivePasting X).level n).apply_zero (s, x))
  simpa only [← Homotopy.path_trans, native_path_apply, carrier_path_apply] using he

/-- Both original target-boundary half-clocks are retained. -/
theorem target_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (((laurentMovement X e).trans (newPositive X e)) s) x =
      (((InputPositiveNull.laurentMovement X).path n x).trans
        ((InputPositiveNull.newPositive X).path n x)) s := by
  have h := positivePasting_native X e n 1 s x
  change CutOpenCarrier.nativeEval _ _ _ _ _ n ((positivePasting X e).toFun (1, s)) x = _ at h
  rw [(positivePasting X e).map_one_left s] at h
  have he := h.trans (((InputPositiveNull.positivePasting X).level n).apply_one (s, x))
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((laurentMovement X e).trans (newPositive X e)) s) x =
      ((InputPositiveNull.laurentMovement X).trans
        (InputPositiveNull.newPositive X)).path n x s at he
  rw [Homotopy.path_trans] at he
  exact he

/-- The entire original positive chart movement on either sheet. -/
theorem positiveMovement_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (positiveMovement X e s) x =
      (InputPositiveNull.positiveMovement X).level n (s, x) :=
  Path.Evaluation.left_factor
    (fun z => CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n z x)
    (positiveMovement X e) (polynomialMovement X e)
    ((InputPositiveNull.positiveMovement X).path n x)
    ((InputPositiveNull.polynomialMovement X).path n x)
    (fun t => source_native X e n t x) s

/-- The unchanged Laurent evaluation edge on either full-reference sheet. -/
theorem laurentMovement_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (laurentMovement X e s) x =
      (InputPositiveNull.laurentMovement X).level n (s, x) :=
  Path.Evaluation.left_factor
    (fun z => CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n z x)
    (laurentMovement X e) (newPositive X e)
    ((InputPositiveNull.laurentMovement X).path n x)
    ((InputPositiveNull.newPositive X).path n x)
    (fun t => target_native X e n t x) s

/-- Both original raw positive binary pieces retain their shared midpoint. -/
theorem newPositive_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (newPositive X e s) x =
      (InputPositiveNull.newPositive X).level n (s, x) :=
  Path.Evaluation.right_factor
    (fun z => CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n z x)
    (laurentMovement X e) (newPositive X e)
    ((InputPositiveNull.laurentMovement X).path n x)
    ((InputPositiveNull.newPositive X).path n x)
    (fun t => target_native X e n t x) s

/-- The polynomial movement is the full original attached evaluation edge. -/
theorem polynomialMovement_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (polynomialMovement X e s) x =
      (InputPositiveNull.polynomialMovement X).level n (s, x) := by
  rw [polynomial_seam]
  exact (InputSeedEvaluationNullCone.cylinder_native X e n s 0 x).trans
    ((InputSeedEvaluationNullCone.nativeSquare X n x).left s)

/-- The original old cone keeps its complete native cylinder coordinate. -/
theorem oldCone_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (oldCone X e s) x =
      (InputPositiveNull.oldCone X).level n (s, x) :=
  (InputSeedEvaluationNullCone.cylinder_native X e n 0 s x).trans
    ((InputSeedEvaluationNullCone.nativeSquare X n x).at_zero s)

/-- The original new cone retains the selected sheet's separate actual tip. -/
theorem newCone_native (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (newCone X e s) x =
      (InputPositiveNull.newCone X).level n (s, x) :=
  (InputSeedEvaluationNullCone.cylinder_native X e n 1 s x).trans
    ((InputSeedEvaluationNullCone.nativeSquare X n x).at_one s)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullRails
