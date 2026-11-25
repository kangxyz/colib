/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleBoundaryRows

/-!
# The actual common face of the first and middle Bass H₁ components

This is the complete four-simplex of common exact-functor data, with the
original center and the two distinct raw normalization intermediates.
Adapted from `H1MiddleJoinFace.lean:23–50` in the original BoundedFlat Bass
proof at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

/-- The five original consecutive vertices at the end of the first component. -/
def firstMiddleFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![26, 27, 28, 29, 30], by decide⟩

/-- The same source path uses these five original middle-component vertices. -/
def middleSourceFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 11, 14, 22], by decide⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- All five dependent reference nodes are shared, including both raw intermediates. -/
theorem middle_path_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v (firstMiddleFace.toOrderHom i) =
      BoundedFlatCoefficientBassH1References.middleNodes P u v (middleSourceFace.toOrderHom i) := by
  fin_cases i
  · exact first_middle_center P u v
  · exact plus_middle_nodes P u v 1
  · exact plus_middle_nodes P u v 2
  · exact minus_middle_nodes P u v 1
  · exact minus_middle_nodes P u v 2

/-- The two original component diagrams have exactly the same complete middle face. -/
theorem middle_face :
    (BoundedFlatCoefficientBassH1Components.firstSimplex P u v).face firstMiddleFace =
      (BoundedFlatCoefficientBassH1Components.middleSimplex P u v).face middleSourceFace := by
  rw [← BoundedFlatCoefficientBassH1References.first_original,
    ← BoundedFlatCoefficientBassH1References.middle_original]
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (middle_path_nodes P u v)

/-- The common boundary itself, retaining the original first-component coordinates. -/
def middleBoundarySimplex :=
  (BoundedFlatCoefficientBassH1Components.firstSimplex P u v).face firstMiddleFace

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
