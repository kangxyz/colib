/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.Topology.HomotopyFiber.BasepointTransport
public import Colib.Topology.HomotopyFiber.WeakContractibility

/-!
# One-connectivity from the original fundamental-group surjection

For connected source and target spaces, Pi zero is bijective. Surjectivity of
the original Pi one map therefore makes the actual fiber at that point path
connected by the proved pointed-set long exact sequence. Actual target paths
transport the conclusion to every fiber and every fiber basepoint.
-/

/-! Adapted from `Quillen/Topology/HomotopyGroups/Connectivity/PiOneSurjective.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [PathConnectedSpace Y]

/-- Surjectivity on original Pi one gives the genuine finite connectivity
property, including nonempty actual fibers and all their degree-zero points. -/
theorem isHomotopyConnectedMap_one_of_piOne_surjective
    (f : C(X, Y)) (x : X) (hf : Function.Surjective (HomotopyGroup.piMap 0 f (x := x) rfl)) :
    IsHomotopyConnectedMap f 1 := by
  let := HomotopyFiber.pathConnectedSpace_of_adjacent f (f x) x rfl
    (homotopyGroupMap_zero_bijective f x).injective hf
  constructor
  · intro y
    exact ⟨HomotopyFiber.basepointTransportEquiv f (PathConnectedSpace.somePath (f x) y)
      (HomotopyFiber.basepoint f (f x) x rfl)⟩
  · intro y z k hk
    have hk₀ : k = 0 := by omega
    subst k
    let e := HomotopyFiber.basepointTransportEquiv f (PathConnectedSpace.somePath y (f x))
    let := subsingleton_homotopyGroup_zero (e z)
    exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl 0).injective.subsingleton

end Topology
