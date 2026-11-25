/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierInputSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierUnitSeams
public import Colib.Topology.Realization.SimplexCubeFaces

/-!
# The exact actual carrier cube for the original global raw identity boundary

All twelve original whole-edge identities are established from actual full reference nodes.
The existing codiscrete-nerve contraction extends precisely this compatible six-face boundary.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity Topology Topology.SimplexCubeExtension
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierCube
variable (X : Scheme.{u})

/-- The original face parameters, read in their literal cube coordinate order. -/
def globalFaces (a : Fin 3 × Bool) : C(Cube, InputIdentityCarrierCharts.Carrier X) :=
  ![if a.2 then ⟨fun x ↦ (InputIdentityCarrierProjection.face X) (x 1, x 2), by fun_prop⟩
      else ⟨fun x ↦ (InputIdentityCarrierCharts.inputFace X) (x 1, x 2), by fun_prop⟩,
    if a.2 then ⟨fun x ↦ (InputIdentityCarrierTop.face X) (x 0, x 2), by fun_prop⟩
      else ⟨fun x ↦ (InputIdentityCarrierBottom.face X) (x 0, x 2), by fun_prop⟩,
    if a.2 then
      ⟨fun x ↦ InputIdentityCarrierCharts.chartFace X minus minus_projection (x 0, x 1),
        by fun_prop⟩
      else
      ⟨fun x ↦ InputIdentityCarrierCharts.chartFace X plus plus_projection (x 0, x 1),
        by fun_prop⟩] a.1

/-- Restrict each unchanged parameter family to its actual intrinsic whole cube face. -/
def faces (a : Fin 3 × Bool) : C(face a, InputIdentityCarrierCharts.Carrier X) :=
  ⟨fun x ↦ globalFaces X a x.val.val, by fun_prop⟩

/-- All twelve nontrivial whole-edge intersections follow from the actual original carrier joins. -/
theorem face_compatible : EdgeCompatible (fun a ↦ faces X a) := by
  intro i j hij b c x hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals cases b <;> cases c
  · change x.val 0 = 0 at hi
    change x.val 1 = 0 at hj
    change (InputIdentityCarrierCharts.inputFace X) (x.val 1, x.val 2) =
      (InputIdentityCarrierBottom.face X) (x.val 0, x.val 2)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierInputSeams.input_bottom X) (x.val 2))
  · change x.val 0 = 0 at hi
    change x.val 1 = 1 at hj
    change (InputIdentityCarrierCharts.inputFace X) (x.val 1, x.val 2) =
      (InputIdentityCarrierTop.face X) (x.val 0, x.val 2)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierInputSeams.input_top X) (x.val 2))
  · change x.val 0 = 1 at hi
    change x.val 1 = 0 at hj
    change (InputIdentityCarrierProjection.face X) (x.val 1, x.val 2) =
      (InputIdentityCarrierBottom.face X) (x.val 0, x.val 2)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.bottom_terminal X) (x.val 2)).symm
  · change x.val 0 = 1 at hi
    change x.val 1 = 1 at hj
    change (InputIdentityCarrierProjection.face X) (x.val 1, x.val 2) =
      (InputIdentityCarrierTop.face X) (x.val 0, x.val 2)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.top_terminal X) (x.val 2)).symm
  · change x.val 0 = 0 at hi
    change x.val 2 = 0 at hj
    change (InputIdentityCarrierCharts.inputFace X) (x.val 1, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierSeams.plus_seam X) (x.val 1))
  · change x.val 0 = 0 at hi
    change x.val 2 = 1 at hj
    change (InputIdentityCarrierCharts.inputFace X) (x.val 1, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierSeams.minus_seam X) (x.val 1))
  · change x.val 0 = 1 at hi
    change x.val 2 = 0 at hj
    change (InputIdentityCarrierProjection.face X) (x.val 1, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierProjection.plus_seam X) (x.val 1))
  · change x.val 0 = 1 at hi
    change x.val 2 = 1 at hj
    change (InputIdentityCarrierProjection.face X) (x.val 1, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierProjection.minus_seam X) (x.val 1))
  · change x.val 1 = 0 at hi
    change x.val 2 = 0 at hj
    change (InputIdentityCarrierBottom.face X) (x.val 0, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.bottom_plus X) (x.val 0))
  · change x.val 1 = 0 at hi
    change x.val 2 = 1 at hj
    change (InputIdentityCarrierBottom.face X) (x.val 0, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.bottom_minus X) (x.val 0))
  · change x.val 1 = 1 at hi
    change x.val 2 = 0 at hj
    change (InputIdentityCarrierTop.face X) (x.val 0, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.top_plus X) (x.val 0))
  · change x.val 1 = 1 at hi
    change x.val 2 = 1 at hj
    change (InputIdentityCarrierTop.face X) (x.val 0, x.val 2) =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection) (x.val 0, x.val 1)
    rw [hi, hj]
    exact (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.top_minus X) (x.val 0))

/-- The accepted exact extension is now applied to the six actual fully compatible carrier faces. -/
def carrierCube : C(Cube, InputIdentityCarrierCharts.Carrier X) :=
  CommonReferenceNerve.fillCubeFaces (InputIdentityNodes.source X) (faces X) (face_compatible X)

/-- The extension keeps every point of each original whole face at its unchanged coordinates. -/
theorem cube_on_face (a : Fin 3 × Bool) (x : Cube) (h : x a.1 = endpoint a.2) :
    carrierCube X x = globalFaces X a x := by
  let xb : boundary := ⟨x, by
    cases hb : a.2 with
    | false => exact ⟨a.1, Or.inl (by
        simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using h)⟩
    | true => exact ⟨a.1, Or.inr (by simpa only [endpoint, hb, ↓reduceIte] using h)⟩⟩
  exact CommonReferenceNerve.fillCubeFaces_face (InputIdentityNodes.source X)
    (faces X) (face_compatible X) a ⟨xb, h⟩

theorem cube_zero (s t : unitInterval) :
    carrierCube X ![0, s, t] = (InputIdentityCarrierCharts.inputFace X) (s, t) :=
  cube_on_face X (0, false) ![0, s, t] rfl

theorem cube_one (s t : unitInterval) :
    carrierCube X ![1, s, t] = (InputIdentityCarrierProjection.face X) (s, t) :=
  cube_on_face X (0, true) ![1, s, t] rfl

theorem cube_bottom (r t : unitInterval) :
    carrierCube X ![r, 0, t] = (InputIdentityCarrierBottom.face X) (r, t) :=
  cube_on_face X (1, false) ![r, 0, t] rfl

theorem cube_top (r t : unitInterval) :
    carrierCube X ![r, 1, t] = (InputIdentityCarrierTop.face X) (r, t) :=
  cube_on_face X (1, true) ![r, 1, t] rfl

theorem cube_left (r s : unitInterval) :
    carrierCube X ![r, s, 0] =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection) (r, s) :=
  cube_on_face X (2, false) ![r, s, 0] rfl

theorem cube_right (r s : unitInterval) :
    carrierCube X ![r, s, 1] =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection) (r, s) :=
  cube_on_face X (2, true) ![r, s, 1] rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierCube
