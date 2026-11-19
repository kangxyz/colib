module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.FiberObstructionStep
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.SimplyConnected

set_option autoImplicit false

open Topology
open scoped Topology

universe u

-- A simply connected pair starts the finite-range induction for its actual map.
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X) :
    IsHomotopyConnectedMap f 1 :=
  isHomotopyConnectedMap_one_of_simplyConnected f x

-- Raising the range kills the next degree at an arbitrary actual fiber point,
-- even though the supplied vanishing only mentions constant-path points.
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (hf : IsHomotopyConnectedMap f (n + 1))
    (hc : ∀ x : X, Subsingleton (HomotopyGroup.Pi (n + 1)
      (HomotopyFiber f (f x)) (HomotopyFiber.basepoint f (f x) x rfl)))
    (y : Y) (z : HomotopyFiber f y) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (HomotopyFiber f y) z) :=
  (hf.succ_of_canonical hc).fiber_subsingleton y z (n + 1) (Nat.lt_succ_self (n + 1))
