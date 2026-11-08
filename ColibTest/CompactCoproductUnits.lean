/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductUnits

/-! # The actual zero-left and zero-right coproduct cylinders on original cubes -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity
open scoped Topology
universe u v
namespace ColibTest.CompactCoproductUnits
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C] (n : ℕ)

/-- Zero on the left uses the literal original second-embedding unit cylinder. -/
theorem original_zero_left
    (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    coproductLeftUnitPath W n q t z = coproductLeftUnitHomotopy W (t, q z) :=
  coproductLeftUnitPath_apply W n q t z

/-- Zero on the right uses the literal original first-embedding unit cylinder. -/
theorem original_zero_right
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    coproductRightUnitPath W n p t z = coproductRightUnitHomotopy W (t, p z) :=
  coproductRightUnitPath_apply W n p t z

/-- Both complete constant-input tracks retain the original constant cube. -/
theorem original_constant_tracks (s t : unitInterval) :
    coproductLeftUnitPath W n GenLoop.const s = GenLoop.const ∧
      coproductRightUnitPath W n GenLoop.const t = GenLoop.const :=
  ⟨coproductLeftUnitPath_const W n s, coproductRightUnitPath_const W n t⟩

/-- An independently varying original input retains its whole spatial boundary. -/
theorem independent_input_boundary
    (P : C(unitInterval, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint))
    (s t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductLeftUnitCubeMap W n (s, P t) z = W.kBasepoint :=
  (coproductLeftUnitCubeMap W n (s, P t)).property z hz

/-- Degree zero retains its original one-coordinate cube and the same complete unit path. -/
theorem original_degree_zero
    (q : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint)
    (t : unitInterval) (z : Fin (0 + 1) → unitInterval) :
    coproductLeftUnitPath W 0 q t z = coproductLeftUnitHomotopy W (t, q z) :=
  coproductLeftUnitPath_apply W 0 q t z

end ColibTest.CompactCoproductUnits
