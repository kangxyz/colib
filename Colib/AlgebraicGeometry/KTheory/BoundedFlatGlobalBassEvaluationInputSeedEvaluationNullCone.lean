/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationCarrier
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveNull
public import Colib.Topology.Path.CarrierConeBoundary
public import Colib.Topology.Prespectrum.RelativeHomotopyTerminalEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation

/-!
# Both original cone-interchange surfaces in the global seed carrier

Each sheet keeps its own tip. The actual polynomial movement and unchanged cone cylinder
supply the entire square. Boundary collapse and terminal-pause cancellation recover the
specified positive-support conePasting at every native level and both independent times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullCone
open CommonReferenceNerve InputSeedEvaluationCarrier
variable (X : Scheme.{u})

/-- Each Boolean chooses one actual cylinder; their terminal tips remain separate. -/
def cylinder (e : Bool) : C(|nerve (Codiscrete (Node (polyRef X)))| × I, Carrier X) :=
  if e then CutOpenCarrier.cylinderPlus (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)
  else CutOpenCarrier.cylinderMinus (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)

/-- The tip belonging to the selected actual polynomial cylinder. -/
def tip (e : Bool) : Carrier X :=
  if e then CutOpenCarrier.tipPlus (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)
  else CutOpenCarrier.tipMinus (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)

/-- Every actual polynomial input ends at the selected tip at cone time one. -/
theorem cylinder_one (e : Bool) (y : |nerve (Codiscrete (Node (polyRef X)))|) :
    cylinder X e (y, 1) = tip X e := by
  cases e
  · exact CutOpenCarrier.cylinderMinus_one _ _ _ _ _ y
  · exact CutOpenCarrier.cylinderPlus_one _ _ _ _ _ y

/-- Native evaluation retains both actual clocks on either sheet. -/
theorem cylinder_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (cylinder X e (movement X r, s)) x =
    (Homotopy.Square.interchange (GlobalSectionChangeIndex.evaluationComparison (projection.app X))
      (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).level n (r, (s, x)) := by
  cases e
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.cylinderMinus _ _ _ _ _ (movement X r, s)) x = _
    rw [CutOpenCarrier.nativeEval_cylinderMinus, movement_native]
    rfl
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.cylinderPlus _ _ _ _ _ (movement X r, s)) x = _
    rw [CutOpenCarrier.nativeEval_cylinderPlus, movement_native]
    rfl

/-- The entire original cylinder over any polynomial movement point. -/
def conePath (e : Bool) (r : I) : Path (cylinder X e (movement X r, 0)) (tip X e) where
  toFun s := cylinder X e (movement X r, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := cylinder_one X e (movement X r)

/-- The unchanged attached movement edge of the selected cone square. -/
def movementEdge (e : Bool) : Path
    (cylinder X e (movement X 0, 0)) (cylinder X e (movement X 1, 0)) where
  toFun r := cylinder X e (movement X r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- Both surfaces are the actual cone cylinder at independent movement and cone times. -/
def square (e : Bool) : CarrierPathSquare.Square
    (conePath X e 0) (conePath X e 1) (movementEdge X e) (Path.refl (tip X e)) where
  parameter := ⟨fun z ↦ cylinder X e (movement X z.1, z.2), by fun_prop⟩
  at_zero _ := rfl
  at_one _ := rfl
  left _ := rfl
  right r := cylinder_one X e (movement X r)

/-- The original cone boundary word includes its exact terminal-pause cancellation. -/
def boundary (e : Bool) : (conePath X e 0).Homotopy
    ((movementEdge X e).trans (conePath X e 1)) := (square X e).coneBoundary

/-- The supported native square retains its original endpoint casts and whole interchange. -/
def nativeSquare (n : ℕ)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CarrierPathSquare.Square ((InputPositiveNull.oldCone X).path n x)
      ((InputPositiveNull.newCone X).path n x)
      ((InputPositiveNull.polynomialMovement X).path n x)
      (Path.refl ((mappingCone (GlobalRawBass.InputIdentityPositive.chart X)).point n)) where
  parameter := ⟨fun z ↦ (Homotopy.Square.interchange
    (GlobalSectionChangeIndex.evaluationComparison (projection.app X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).level n
      (z.1, (z.2, x)), by fun_prop⟩
  at_zero s := (Homotopy.Square.interchange
    (GlobalSectionChangeIndex.evaluationComparison (projection.app X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).at_zero n s x
  at_one s := (Homotopy.Square.interchange
    (GlobalSectionChangeIndex.evaluationComparison (projection.app X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).at_one n s x
  left r := (Homotopy.Square.interchange
    (GlobalSectionChangeIndex.evaluationComparison (projection.app X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).left n r x
  right r := (Homotopy.Square.interchange
    (GlobalSectionChangeIndex.evaluationComparison (projection.app X))
    (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).right n r x

/-- Entire-square evaluation retains the full collapse and cancellation of the actual boundary. -/
theorem boundary_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (boundary X e (r, s)) x =
        (nativeSquare X n x).coneBoundary (r, s) :=
  (square X e).coneBoundary_natural (nativeSquare X n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n y x) (fun r s ↦ cylinder_native X e n r s x) r s

private theorem relativeTrans_apply {E F : LoopPrespectrum.{u}}
    {f h : E ⟶ F} {H K L : Homotopy f h}
    (J : H.RelHomotopy K) (J' : K.RelHomotopy L) (n : ℕ) (r s : I) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) = ((J.level n).trans (J'.level n)) (r, (s, x)) := rfl

/-- Both original halves are exactly the specified supported conePasting, without a new recipe. -/
theorem nativeSquare_conePasting (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    (nativeSquare X n x).coneBoundary (r, s) =
      (InputPositiveNull.conePasting X).level n (r, (s, x)) := by
  rw [CarrierPathSquare.Square.coneBoundary_apply]
  unfold InputPositiveNull.conePasting
  rw [relativeTrans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with h
  · rw [Homotopy.RelHomotopy.ofLevels_apply, Homotopy.Square.toBoundary_apply]
    rfl
  · rw [Homotopy.RelHomotopy.transRefl_apply_path, Homotopy.path_trans]

/-- Each whole carrier boundary recovers the specified supported comparison at all times. -/
theorem boundary_conePasting (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (boundary X e (r, s)) x =
        (InputPositiveNull.conePasting X).level n (r, (s, x)) :=
  (boundary_native X e n r s x).trans (nativeSquare_conePasting X n r s x)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullCone
