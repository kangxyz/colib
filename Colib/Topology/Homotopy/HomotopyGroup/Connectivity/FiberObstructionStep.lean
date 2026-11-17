/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.Topology.HomotopyFiber.BasepointTransport
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-!
# Promote a canonical fiber obstruction to every actual fiber point

Positive connectivity makes each actual path-space fiber path connected. The
stored path of an arbitrary fiber point transports it to the fiber over its
own source image; an actual path in that fiber then compares its basepoint
with the canonical constant-path point. No continuously chosen paths or new
relative-homotopy model are used.

-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/FiberObstructionStep.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; the original maps, bounds, fibers and
basepoints are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : C(X, Y)} {n : ℕ}

/-- Each actual fiber of a positively connected original map is path connected. -/
theorem IsHomotopyConnectedMap.fiber_pathConnectedSpace
    (hf : IsHomotopyConnectedMap f (n + 1)) (y : Y) :
    PathConnectedSpace (HomotopyFiber f y) := by
  let z := Classical.choice (hf.fiber_nonempty y)
  let : Subsingleton (HomotopyGroup.Pi 0 (HomotopyFiber f y) z) :=
    hf.fiber_subsingleton y z 0 (by omega)
  let : Subsingleton (ZerothHomotopy (HomotopyFiber f y)) :=
    (HomotopyGroup.pi0EquivZerothHomotopy
      (X := HomotopyFiber f y) (x := z)).symm.injective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨ZerothHomotopy.mk z⟩, inferInstance⟩

/-- Canonical source-image fiber vanishing implies vanishing at every actual
fiber basepoint, using its own stored path and a genuine fiber path. -/
theorem IsHomotopyConnectedMap.fiber_subsingleton_of_canonical
    (hf : IsHomotopyConnectedMap f (n + 1)) (k : ℕ)
    (hcanonical : ∀ x : X, Subsingleton (HomotopyGroup.Pi k
      (HomotopyFiber f (f x)) (HomotopyFiber.basepoint f (f x) x rfl)))
    (y : Y) (z : HomotopyFiber f y) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f y) z) := by
  let x := z.val.1
  let e : ContinuousMap.HomotopyEquiv (HomotopyFiber f y) (HomotopyFiber f (f x)) :=
    HomotopyFiber.basepointTransportEquiv f (HomotopyFiber.toPath f y z).symm
  let b := HomotopyFiber.basepoint f (f x) x rfl
  let : PathConnectedSpace (HomotopyFiber f (f x)) := hf.fiber_pathConnectedSpace (f x)
  let : Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f (f x)) b) := hcanonical x
  have htarget : Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f (f x)) (e z)) :=
    (pathTransport (PathConnectedSpace.joined b (e z)).somePath k).symm.injective.subsingleton
  exact ⟨fun a b ↦ (homotopyGroupMap_bijective_of_homotopyEquiv e
    (x := z) (y := e z) rfl k).injective (@Subsingleton.elim _ htarget _ _)⟩

/-- Kill the next obstruction while retaining actual nonemptiness and every
already known lower degree, at all original target and fiber basepoints. -/
theorem IsHomotopyConnectedMap.succ_of_canonical
    (hf : IsHomotopyConnectedMap f (n + 1))
    (hcanonical : ∀ x : X, Subsingleton (HomotopyGroup.Pi (n + 1)
      (HomotopyFiber f (f x)) (HomotopyFiber.basepoint f (f x) x rfl))) :
    IsHomotopyConnectedMap f (n + 2) where
  fiber_nonempty := hf.fiber_nonempty
  fiber_subsingleton y z k hk := by
    by_cases hlow : k < n + 1
    · exact hf.fiber_subsingleton y z k hlow
    · have heq : k = n + 1 := by omega
      subst k
      exact hf.fiber_subsingleton_of_canonical (n + 1) hcanonical y z

end Topology
