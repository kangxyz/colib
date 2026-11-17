module

public import Colib.Topology.PlusConstruction.DisplayedComparisonWeakEquivalence

set_option autoImplicit false

open Topology
open scoped Topology

universe u

-- A supplied target covering and the literal marked lift suffice to detect k itself.
example {X Y Z E : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace E] [SimplyConnectedSpace E]
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    (q : C(E, Z)) (hq : IsCoveringMap q) (e : E) (he : k y = q e)
    (p : Y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) k (x := p) rfl) :=
  (IsPlusConstruction.displayedComparison_isWeakHomotopyEquivalence_of_cover
    f g k H γ δ N hf hg q hq e he).homotopy_bijective p n
