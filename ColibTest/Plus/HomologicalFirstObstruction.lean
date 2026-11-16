module

public import Colib.Topology.HomotopyCofiber.HomologicalFirstObstruction

set_option autoImplicit false

open CategoryTheory FundamentalGroupoid.LocalCoefficients Topology Topology.ReducedMappingCone
open scoped Topology

universe u

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y))

-- At the first step the actual integral chain map kills actual fiber Pi one.
example (x : X) (h₁ : IsHomotopyConnectedMap f 1)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficients.{u}))) :
    Subsingleton (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) :=
  subsingleton_firstObstruction_of_integral_quasiIso f x 0 h₁ hH

-- The one-degree improvement applies at every target and original fiber point.
example (m : ℕ) (h : IsHomotopyConnectedMap f (m + 1))
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficients.{u})))
    (y : Y) (z : HomotopyFiber f y) :
    Subsingleton (HomotopyGroup.Pi (m + 1) (HomotopyFiber f y) z) :=
  (isHomotopyConnectedMap_succ_of_integral_quasiIso f m h hH).fiber_subsingleton
    y z (m + 1) (Nat.lt_succ_self (m + 1))

end
