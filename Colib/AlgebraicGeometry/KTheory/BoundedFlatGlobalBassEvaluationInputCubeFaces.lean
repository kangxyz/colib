/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartTargetSeams
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterSource
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterChart
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterTarget
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputLaurentSeams

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCubeExtension

/-!
# The six complete original mixed evaluation faces

Twelve proved equalities in the fixed common-reference carrier glue the six actual faces.
The existing nerve contraction extends that precise boundary without modifying any face,
clock, full Model arrow, or reference anchor.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity Topology.SimplexCubeExtension
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCubeFaces
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The first edge of the entire target face is the terminal original Laurent evaluation. -/
theorem target_laurent (s : unitInterval) :
    InputTargetFace.parameter g (0, s) = InputLaurentFace.parameter g (1, s) :=
  (Topology.ScalarRectangle.concatFirst_zero _ _ (InputRawPastedSeam.seam g) s).trans
    (InputLaurentSeams.post_source_face g s)

/-- The original face parameters, read in their literal cube coordinate order. -/
def globalFaces (a : Fin 3 × Bool) :
    C(Cube, |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  ![if a.2 then ⟨fun x ↦ (InputTargetFace.parameter g) (x 1, x 2), by fun_prop⟩
      else ⟨fun x ↦ (InputMixedDesc.preSquareParameter g) (x 1, x 2), by fun_prop⟩,
    if a.2 then ⟨fun x ↦ (InputSpanParameterWord.parameter g) (x 0, x 2), by fun_prop⟩
      else ⟨fun x ↦ (InputLaurentFace.parameter g) (x 0, x 2), by fun_prop⟩,
    if a.2 then ⟨fun x ↦ (InputChartSquareParameter.minusParameter g) (x 0, x 1), by fun_prop⟩
      else ⟨fun x ↦ (InputChartSquareParameter.plusParameter g) (x 0, x 1), by fun_prop⟩] a.1

/-- Restrict each unchanged parameter family to its actual intrinsic whole cube face. -/
def faces (a : Fin 3 × Bool) :
    C(face a, |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  ⟨fun x ↦ globalFaces g a x.val.val, by fun_prop⟩

/-- All twelve nontrivial whole-edge intersections follow from the actual original scalar joins. -/
theorem face_compatible : EdgeCompatible (fun a ↦ faces g a) := by
  intro i j hij b c x hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals cases b <;> cases c
  · change x.val 0 = 0 at hi
    change x.val 1 = 0 at hj
    change (InputMixedDesc.preSquareParameter g) (x.val 1, x.val 2) =
      (InputLaurentFace.parameter g) (x.val 0, x.val 2)
    rw [hi, hj]
    exact InputLaurentSeams.source_face g (x.val 2)
  · change x.val 0 = 0 at hi
    change x.val 1 = 1 at hj
    change (InputMixedDesc.preSquareParameter g) (x.val 1, x.val 2) =
      (InputSpanParameterWord.parameter g) (x.val 0, x.val 2)
    rw [hi, hj]
    exact InputSpanParameterSeams.source g (x.val 2)
  · change x.val 0 = 1 at hi
    change x.val 1 = 0 at hj
    change (InputTargetFace.parameter g) (x.val 1, x.val 2) =
      (InputLaurentFace.parameter g) (x.val 0, x.val 2)
    rw [hi, hj]
    exact target_laurent g (x.val 2)
  · change x.val 0 = 1 at hi
    change x.val 1 = 1 at hj
    change (InputTargetFace.parameter g) (x.val 1, x.val 2) =
      (InputSpanParameterWord.parameter g) (x.val 0, x.val 2)
    rw [hi, hj]
    exact InputSpanParameterSeams.target g (x.val 2)
  · change x.val 0 = 0 at hi
    change x.val 2 = 0 at hj
    change (InputMixedDesc.preSquareParameter g) (x.val 1, x.val 2) =
      (InputChartSquareParameter.plusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact InputChartFaceSeams.pre_plus g (x.val 1)
  · change x.val 0 = 0 at hi
    change x.val 2 = 1 at hj
    change (InputMixedDesc.preSquareParameter g) (x.val 1, x.val 2) =
      (InputChartSquareParameter.minusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact InputChartFaceSeams.pre_minus g (x.val 1)
  · change x.val 0 = 1 at hi
    change x.val 2 = 0 at hj
    change (InputTargetFace.parameter g) (x.val 1, x.val 2) =
      (InputChartSquareParameter.plusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact InputChartTargetSeams.plus g (x.val 1)
  · change x.val 0 = 1 at hi
    change x.val 2 = 1 at hj
    change (InputTargetFace.parameter g) (x.val 1, x.val 2) =
      (InputChartSquareParameter.minusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact InputChartTargetSeams.minus g (x.val 1)
  · change x.val 1 = 0 at hi
    change x.val 2 = 0 at hj
    change (InputLaurentFace.parameter g) (x.val 0, x.val 2) =
      (InputChartSquareParameter.plusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (InputLaurentSeams.plus_seam g (x.val 0)).symm
  · change x.val 1 = 0 at hi
    change x.val 2 = 1 at hj
    change (InputLaurentFace.parameter g) (x.val 0, x.val 2) =
      (InputChartSquareParameter.minusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (InputLaurentSeams.minus_seam g (x.val 0)).symm
  · change x.val 1 = 1 at hi
    change x.val 2 = 0 at hj
    change (InputSpanParameterWord.parameter g) (x.val 0, x.val 2) =
      (InputChartSquareParameter.plusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact InputSpanParameterSeams.plus g (x.val 0)
  · change x.val 1 = 1 at hi
    change x.val 2 = 1 at hj
    change (InputSpanParameterWord.parameter g) (x.val 0, x.val 2) =
      (InputChartSquareParameter.minusParameter g) (x.val 0, x.val 1)
    rw [hi, hj]
    exact InputSpanParameterSeams.minus g (x.val 0)

/-- The accepted exact extension is now applied to the six actual fully compatible scalar faces. -/
def parameter :
    C(Cube, |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  CommonReferenceNerve.fillCubeFaces (InputMixedDesc.sourceMap g) (faces g) (face_compatible g)

/-- The extension keeps every point of each original whole face at its unchanged coordinates. -/
theorem cube_on_face (a : Fin 3 × Bool) (x : Cube) (h : x a.1 = endpoint a.2) :
    parameter g x = globalFaces g a x := by
  let xb : Topology.SimplexCubeExtension.boundary := ⟨x, by
    cases hb : a.2 with
    | false => exact ⟨a.1, Or.inl (by
        simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using h)⟩
    | true => exact ⟨a.1, Or.inr (by simpa only [endpoint, hb, ↓reduceIte] using h)⟩⟩
  exact CommonReferenceNerve.fillCubeFaces_face (InputMixedDesc.sourceMap g)
    (faces g) (face_compatible g) a ⟨xb, h⟩

theorem zero (s t : unitInterval) :
    parameter g ![0, s, t] = (InputMixedDesc.preSquareParameter g) (s, t) :=
  cube_on_face g (0, false) ![0, s, t] rfl

theorem one (s t : unitInterval) :
    parameter g ![1, s, t] = (InputTargetFace.parameter g) (s, t) :=
  cube_on_face g (0, true) ![1, s, t] rfl

theorem bottom (r t : unitInterval) :
    parameter g ![r, 0, t] = (InputLaurentFace.parameter g) (r, t) :=
  cube_on_face g (1, false) ![r, 0, t] rfl

theorem top (r t : unitInterval) :
    parameter g ![r, 1, t] = (InputSpanParameterWord.parameter g) (r, t) :=
  cube_on_face g (1, true) ![r, 1, t] rfl

theorem plus (r s : unitInterval) :
    parameter g ![r, s, 0] = (InputChartSquareParameter.plusParameter g) (r, s) :=
  cube_on_face g (2, false) ![r, s, 0] rfl

theorem minus (r s : unitInterval) :
    parameter g ![r, s, 1] = (InputChartSquareParameter.minusParameter g) (r, s) :=
  cube_on_face g (2, true) ![r, s, 1] rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCubeFaces
