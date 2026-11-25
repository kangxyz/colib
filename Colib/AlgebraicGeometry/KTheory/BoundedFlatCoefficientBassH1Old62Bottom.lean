/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedBoundary
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1BottomJoinScalar

/-!
# The original H₁ source face in the common Bass 62-simplex

The fixed bottom product's final column is exactly the first H₁ source
four-simplex. This keeps its full diagram and original scalar speed, not
just its endpoints. Adapted from `H1BottomJoinFace.lean` at Quillen commit
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

open BoundedFlatCoefficientBassH0Merged

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

/-- The fixed bottom product's actual terminal column inside the common 62-simplex. -/
def oldBottomEdgeFace : ⦋4⦌ ⟶ ⦋62⦌ := SimplexGrid.columnFace 4 2 2 ≫ supportedBottomFace

/-- The unchanged terminal-column parameter in the common 62 coordinates. -/
theorem old_bottom_edge_parameter (t : unitInterval) :
    StdSimplex.map oldBottomEdgeFace.toOrderHom
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t) =
      bottomParameter.{u} (1, t) := by
  change StdSimplex.map oldBottomEdgeFace.toOrderHom
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t) =
    StdSimplex.map oldIndex
      (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
        (BoundedFlatCoefficientBassLaurentBottomFace.parameter.{u} (1, t)))
  rw [bottom_target_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp]; rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Restrictions to the retained bottom face and its terminal column compose as whole diagrams. -/
private theorem bottom_column_face :
    ((simplex P u v).face supportedBottomFace).face (SimplexGrid.columnFace 4 2 2) =
      (simplex P u v).face oldBottomEdgeFace := by
  apply ModelSimplex.ext_diagram
  rfl

/-- The first H₁ source and the old bottom target are the same entire four-simplex. -/
theorem first_old62_bottom_face :
    (BoundedFlatCoefficientBassH1Components.firstSimplex P u v).face middleSourceFace =
      (simplex P u v).face oldBottomEdgeFace := by
  rw [first_bottom_face, ← bottom_face P u v]; exact bottom_column_face P u v

/-- Transport of every original terminal-column value to the first H₁ source. -/
theorem old62_first_bottom_scalar (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (bottomParameter.{u} (1, t), x) =
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH1Components.firstSimplex P u v) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (0, t), x) := by
  rw [← old_bottom_edge_parameter, prespectrumSimplexFamily_face, ← first_old62_bottom_face,
    ← prespectrumSimplexFamily_face, middle_source_parameter]

/-- The whole old bottom edge evaluates to the prescribed source of the original pasted H₁. -/
theorem old62_h1_source_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (bottomParameter.{u} (1, t), x) =
    (boundedAboveFlatCoefficientBassCompositeComparison P u v).level n
      (0, HomotopyPushout.cylinder
        (K (polynomialProjection P a)) (K (polynomialProjection P a)) n (t, x)) := by
  have hz : leftHalf 0 = 0 := by
    apply Subtype.ext
    simp [coe_leftHalf]
  rw [old62_first_bottom_scalar P u v n t x]
  simpa only [hz] using BoundedFlatCoefficientBassH1NativeCells.first_native P u v n 0 t x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
