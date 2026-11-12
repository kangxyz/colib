/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Equiv.Based
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Actual compact-open loops preserve based homotopy equivalences

Loop the displayed based maps and their point-fixed inverse homotopies
pointwise. The construction uses the unchanged compact-open path topology,
not a weak loop-space approximation or induced maps on homotopy groups.
-/

open Topology

/-! Implementation source: `Quillen/Topology/HomotopyEquiv/BasedLoop.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u v
namespace Topology.BasedHomotopyEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Pointwise looping of the original left inverse homotopy. -/
def loopLeftHomotopy (e : BasedHomotopyEquiv x y) :
    ((basedLoopMap e.invMap e.inv_point).comp (basedLoopMap e.toMap e.map_point)).Homotopy
      (ContinuousMap.id (Path x x)) where
  toFun z := {
    toFun t := e.leftHomotopy (z.1, z.2 t)
    continuous_toFun := by fun_prop
    source' := by rw [z.2.source]; exact e.left_fixed z.1
    target' := by rw [z.2.target]; exact e.left_fixed z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × Path x x) × I ↦
      e.leftHomotopy (z.1.1, z.1.2 z.2))
    fun_prop
  map_zero_left γ := by
    apply Path.ext
    funext t
    exact e.leftHomotopy.apply_zero (γ t)
  map_one_left γ := by
    apply Path.ext
    funext t
    exact e.leftHomotopy.apply_one (γ t)

/-- Pointwise looping of the original right inverse homotopy. -/
def loopRightHomotopy (e : BasedHomotopyEquiv x y) :
    ((basedLoopMap e.toMap e.map_point).comp (basedLoopMap e.invMap e.inv_point)).Homotopy
      (ContinuousMap.id (Path y y)) where
  toFun z := {
    toFun t := e.rightHomotopy (z.1, z.2 t)
    continuous_toFun := by fun_prop
    source' := by rw [z.2.source]; exact e.right_fixed z.1
    target' := by rw [z.2.target]; exact e.right_fixed z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × Path y y) × I ↦
      e.rightHomotopy (z.1.1, z.1.2 z.2))
    fun_prop
  map_zero_left γ := by
    apply Path.ext
    funext t
    exact e.rightHomotopy.apply_zero (γ t)
  map_one_left γ := by
    apply Path.ext
    funext t
    exact e.rightHomotopy.apply_one (γ t)

/-- The two original based loop maps are genuine continuous homotopy inverses. -/
def loopHomotopyEquiv (e : BasedHomotopyEquiv x y) :
    ContinuousMap.HomotopyEquiv (Path x x) (Path y y) where
  toFun := basedLoopMap e.toMap e.map_point
  invFun := basedLoopMap e.invMap e.inv_point
  left_inv := ⟨e.loopLeftHomotopy⟩
  right_inv := ⟨e.loopRightHomotopy⟩

@[simp]
theorem loopHomotopyEquiv_toFun (e : BasedHomotopyEquiv x y) :
    e.loopHomotopyEquiv.toFun = basedLoopMap e.toMap e.map_point := rfl

theorem loopHomotopyEquiv_refl (e : BasedHomotopyEquiv x y) :
    e.loopHomotopyEquiv (Path.refl x) = Path.refl y :=
  basedLoopMap_refl e.toMap e.map_point

/-- The looped left inverse homotopy retains the constant-loop basepoint. -/
theorem loopLeftHomotopy_refl (e : BasedHomotopyEquiv x y) (t : I) :
    e.loopLeftHomotopy (t, Path.refl x) = Path.refl x := by
  apply Path.ext
  funext s
  exact e.left_fixed t

/-- The looped right inverse homotopy retains the constant-loop basepoint. -/
theorem loopRightHomotopy_refl (e : BasedHomotopyEquiv x y) (t : I) :
    e.loopRightHomotopy (t, Path.refl y) = Path.refl y := by
  apply Path.ext
  funext s
  exact e.right_fixed t

end Topology.BasedHomotopyEquiv
