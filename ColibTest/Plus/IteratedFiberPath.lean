module

import Colib.Topology.HomotopyFiber.IteratedFiberPath

/-!
# The literal double fiber with an arbitrary endpoint path

The incoming path is not taken constant. The comparison prefixes the entire
given path to the loop, leaves the outer path constant, and retains the original
chosen point in the unit-removal track.
-/

open Topology Topology.HomotopyFiber
open scoped Topology unitInterval

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (b : B) (x : E) (γ : Path (p x) b)

example (δ : Path b b) :
    (loopsToIteratedFiberPathEquiv p b x γ δ).1.1.1.2 = (γ.trans δ).toContinuousMap :=
  loopsToIteratedFiberPathEquiv_innerPath p b x γ δ

example (δ : Path b b) :
    (loopsToIteratedFiberPathEquiv p b x γ δ).1.2 = ContinuousMap.const unitInterval x :=
  loopsToIteratedFiberPathEquiv_outerPath p b x γ δ

noncomputable example :
    Path (loopsToIteratedFiberPathEquiv p b x γ (Path.refl b))
      (basepoint (projection p b) x (pointWithPath p x b γ) rfl) :=
  loopsToIteratedFiberPathUnitPath p b x γ

noncomputable example (z : HomotopyFiber (projection p b) x) (k : ℕ) :
    HomotopyGroup.Pi k (HomotopyFiber (projection p b) x) z ≃ HomotopyGroup.Pi (k + 1) B b :=
  iteratedFiberPiEquivOfPath p b x γ z k
