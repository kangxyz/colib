module

public import Colib.Topology.Realization.SimplexBoundaryFilling
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection

open Convexity
open scoped Topology unitInterval

namespace Convexity.StdSimplex

universe u

variable {Z : Type u} [TopologicalSpace Z]

example [PathConnectedSpace Z] (f g : C(StdSimplex ℝ (Fin 1), Z))
    (H : C(boundary 0 × I, Z))
    (hzero : ∀ b : boundary 0, H (b, 0) = f b.val)
    (hone : ∀ b : boundary 0, H (b, 1) = g b.val) :
    ∃ K : f.Homotopy g, ∀ (b : boundary 0) (t : I), K (t, b.val) = H (b, t) :=
  exists_simplex_homotopy_of_boundary 0 Topology.subsingleton_homotopyGroup_zero
    f g H hzero hone

example (d : ℕ) (hs : ∀ z : Z, Subsingleton (HomotopyGroup.Pi (d + 1) Z z))
    (f g : C(StdSimplex ℝ (Fin (d + 2)), Z))
    (H : C(boundary (d + 1) × I, Z))
    (hzero : ∀ b : boundary (d + 1), H (b, 0) = f b.val)
    (hone : ∀ b : boundary (d + 1), H (b, 1) = g b.val) :
    ∃ K : f.Homotopy g, ∀ (b : boundary (d + 1)) (t : I), K (t, b.val) = H (b, t) :=
  exists_simplex_homotopy_of_boundary (d + 1) hs f g H hzero hone

#print axioms exists_simplex_homotopy_of_boundary

end Convexity.StdSimplex
