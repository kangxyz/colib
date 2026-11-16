module

import Colib.Topology.HomotopyFiber.WeakSourcePositive

/-!
# Positive source change on actual homotopy fibers

The regression uses independent universes for both total spaces and the common
base, and retains the given source-change map and based path on the literal fiber.
In particular, the range starts at the fundamental group, not a pointed set.
-/

open Topology Topology.HomotopyFiber

universe u v w

variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]

example (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (h : g.comp u = f)
    (x : X) (b : B) (hx : f x = b)
    (h₁ : Function.Bijective (HomotopyGroup.piMap 0 u (x := x) rfl))
    (h₂ : Function.Surjective (HomotopyGroup.piMap 1 u (x := x) rfl)) :
    Function.Bijective (HomotopyGroup.piMap 0 (mapOver f g u h b)
      (mapOver_basepoint f g u h x b hx)) :=
  piMap_mapOver_bijective f g u h x b hx 0 h₁ h₂
