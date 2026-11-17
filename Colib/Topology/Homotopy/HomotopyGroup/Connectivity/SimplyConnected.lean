/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Vanishing
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The initial connectivity range for simply connected spaces

Simple connectedness kills the actual finite homotopy sets in degrees zero and one.
Consequently the original map to a point is two-connected, while an arbitrary map between
simply connected spaces is one-connected. These statements use the actual homotopy fibers;
they contain no homological recognition assumption.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/SimplyConnected.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; the original maps, bounds, fibers and
basepoints are retained. -/
@[expose] public section
noncomputable section

universe u
namespace Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The first homotopy group vanishes by its genuine fundamental-group comparison. -/
theorem subsingleton_homotopyGroup_one_of_simplyConnected [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 1 X x) :=
  (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).injective.subsingleton

/-- Both finite homotopy sets strictly below degree two vanish. -/
theorem subsingleton_homotopyGroup_lt_two_of_simplyConnected [SimplyConnectedSpace X]
    (x : X) (k : ℕ) (hk : k < 2) : Subsingleton (HomotopyGroup.Pi k X x) := by
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl
  · exact subsingleton_homotopyGroup_zero x
  · exact subsingleton_homotopyGroup_one_of_simplyConnected x

/-- Simple connectedness gives exactly the two-connected map to the actual point space. -/
theorem isHomotopyConnectedMap_const_two_of_simplyConnected [SimplyConnectedSpace X]
    (x : X) : IsHomotopyConnectedMap
      (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) 2 :=
  isHomotopyConnectedMap_const_of_vanishing x 2
    (subsingleton_homotopyGroup_lt_two_of_simplyConnected)

/-- An arbitrary original map between simply connected spaces starts the connectivity induction. -/
theorem isHomotopyConnectedMap_one_of_simplyConnected
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X) :
    IsHomotopyConnectedMap f 1 :=
  isHomotopyConnectedMap_of_vanishing f x 1
    (fun a k hk ↦ subsingleton_homotopyGroup_lt_two_of_simplyConnected a k (by omega))
    (fun b k hk ↦ subsingleton_homotopyGroup_lt_two_of_simplyConnected b k (by omega))

end Topology
