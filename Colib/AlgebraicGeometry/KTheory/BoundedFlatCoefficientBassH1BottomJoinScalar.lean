/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1BottomJoin
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1NativeUnaryCells

/-!
# The original scalar path where the first Bass H₁ face meets the Laurent bottom

The actual terminal column and the actual source edge use the same
four-simplex at the original speed. In every prespectrum level this
recovers the source of the original pasted Bass homotopy as well as
the target of the Laurent composition family. Adapted from
`H1BottomJoinFace.lean` in the original BoundedFlat Bass proof at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open FundamentalGroupoid.OpenCover
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

/-- The actual last column of the Laurent grid retains the whole original projection path. -/
theorem bottom_target_parameter (t : unitInterval) :
    BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (1, t) =
      StdSimplex.map (SimplexGrid.columnFace 4 2 2).toOrderHom
        (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t) := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (BoundedFlatCoefficientBassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target]
  exact SimplexGrid.parameter_column 4 2 2 _

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The native scalar evaluation on the bottom terminal column equals that on the first source. -/
theorem first_bottom_scalar (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v) n
      (BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (1, t), x) =
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH1Components.firstSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (0, t), x) := by
  rw [bottom_target_parameter t, ← middle_source_parameter t]
  let z := BoundedFlatPerfectNativeSquareFiveSimplex.parameter t
  let y : (prespectrum (asSmallCategory (W (space (op P, a))))).space n := x
  have bottomEval := prespectrumSimplexFamily_face
    (BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v) (SimplexGrid.columnFace 4 2 2) n z y
  have firstEval := prespectrumSimplexFamily_face
    (BoundedFlatCoefficientBassH1Components.firstSimplex P u v) middleSourceFace n z y
  have faceEval := congrArg (fun S ↦ prespectrumSimplexFamily S n (z, y))
    (first_bottom_face P u v)
  exact bottomEval.trans (faceEval.symm.trans firstEval.symm)

/-- The original bottom terminal column evaluates to the actual source of the pasted comparison. -/
theorem bottom_h1_source_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v) n
      (BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (1, t), x) =
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (0, HomotopyPushout.cylinder
        (K (polynomialProjection P a)) (K (polynomialProjection P a)) n (t, x)) := by
  have hz : leftHalf 0 = 0 := by
    apply Subtype.ext
    simp [coe_leftHalf]
  rw [first_bottom_scalar P u v n t x]
  simpa only [hz] using BoundedFlatCoefficientBassH1NativeCells.first_native P u v n 0 t x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
