module

public import Colib.Topology.HomotopyPullback.PathProjectionLifting

open Topology Topology.HomotopyPullback
open scoped Topology unitInterval

universe u v

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B))

example (hp : CubicalSubdivision.BoundaryLifting p) :
    CubicalSubdivision.BoundaryLifting (pathProjection p) :=
  hp.pathProjection

example {X : Type v} [TopologicalSpace X]
    (a₀ a₁ : C(X, E)) (H : (p.comp a₀).Homotopy (p.comp a₁))
    (l : C(X, C(I, E))) (hl : (pathProjection p).comp l = homotopyTarget p a₀ a₁ H)
    (x : X) (t : I) :
    (∃ K : a₀.Homotopy a₁, p (K (t, x)) = H (t, x)) :=
  ⟨homotopyOfPathProjectionLift p a₀ a₁ H l hl,
    homotopyOfPathProjectionLift_project p a₀ a₁ H l hl t x⟩

#print axioms CubicalSubdivision.BoundaryLifting.pathProjection
#print axioms homotopyOfPathProjectionLift_project
