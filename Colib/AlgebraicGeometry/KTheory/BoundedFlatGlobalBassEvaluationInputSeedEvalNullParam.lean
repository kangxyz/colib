/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvalBinary
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNullParam

/-! The original split null path on each separate sheet at a moving evaluation input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalNull
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier InputSeedInputNull
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The whole source rail of the original split binary path on the chosen sheet. -/
def source (e : Bool) : C(I, Carrier g) :=
  ⟨fun r ↦ sheet g e (InputSeedEvalBinary.parameter g (r, 0)), by fun_prop⟩

/-- The whole binary-to-polynomial seam, before starting the original cone cylinder. -/
def middle (e : Bool) : C(I, Carrier g) :=
  ⟨fun r ↦ sheet g e (InputSeedEvalBinary.parameter g (r, 1)), by fun_prop⟩

/-- Both binary halves keep their original clock while the evaluation time varies. -/
def binarySwap (e : Bool) : (source g e).Homotopy (middle g e) where
  toFun z := sheet g e (InputSeedEvalBinary.parameter g (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The second null half is the original cylinder over the moving polynomial edge. -/
def cylinderSwap (e : Bool) :
    (middle g e).Homotopy (ContinuousMap.const I (tip g e)) where
  toFun z := cylinder g e (InputSeedEvalBinary.polynomialParameter g z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (cylinder_zero g e _).trans
    (congrArg (sheet g e) (InputSeedEvalBinary.target_attachment g r).symm)
  map_one_left _ := cylinder_one g e _

/-- The exact original binary/cylinder null, retaining its prescribed half cut. -/
def nullSwap (e : Bool) :
    (source g e).Homotopy (ContinuousMap.const I (tip g e)) :=
  (binarySwap g e).trans (cylinderSwap g e)

/-- Evaluation time and null time are independent parameters on each separate sheet. -/
def parameter (e : Bool) : C(I × I, Carrier g) :=
  ⟨fun z ↦ nullSwap g e (z.2, z.1), by fun_prop⟩

/-- The entire lower edge is the actual binary source rail. -/
theorem zero (e : Bool) (r : I) : parameter g e (r, 0) = source g e r :=
  (nullSwap g e).apply_zero r

/-- The entire upper edge is the original distinct tip for the chosen sheet. -/
theorem one (e : Bool) (r : I) : parameter g e (r, 1) = tip g e :=
  (nullSwap g e).apply_one r

/-- At every evaluation time the scalar null is an actual path to its own tip. -/
def path (e : Bool) (r : I) : Path (source g e r) (tip g e) where
  toFun s := parameter g e (r, s)
  continuous_toFun := by fun_prop
  source' := zero g e r
  target' := one g e r

/-- No additional clock or replacement path is inserted into the actual null. -/
theorem path_apply (e : Bool) (r s : I) : path g e r s = nullSwap g e (s, r) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvalNull
