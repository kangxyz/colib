module

public import Colib.Topology.Realization.RelativeSphericalStraightening

open Convexity Topology
open scoped Topology unitInterval

namespace Convexity.StdSimplex

universe u

variable {Z : Type u} [TopologicalSpace Z]

example [PathConnectedSpace Z] (n : ℕ) (z : Z) (f : SphericalSimplex Z z n)
    (b : Finset C(StdSimplex ℝ (Fin (n + 2)), Z))
    (hs : ∀ x : Z, ∀ k : ℕ, 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k Z x)) :
    ∃ P : PartialSimplexStraightening n z (sphericalStraighteningFamily f b)
        (sphericalStraighteningFixedFamily f) (sphericalStraighteningFamily_faceClosed f b)
        (n + 2),
      ∀ x t, P.track n ⟨f.val, sphericalStraighteningFixedFamily_subset f b n
        (mem_sphericalStraighteningFixedFamily_input f)⟩ (x, t) = f x := by
  obtain ⟨P⟩ := exists_relative_spherical_straightening n z f b hs
  exact ⟨P, fun x t ↦ P.stationary n _ (mem_sphericalStraighteningFixedFamily_input f) x t⟩

example {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}
    (P : PartialSimplexStraightening n z S F hS N) (hn : n + 1 < N)
    (τ : {τ // τ ∈ S (n + 1)}) (i : Fin (n + 2)) :
    sphericalFace (P.endpoint (n + 1) τ) (P.endpoint_skeleton (n + 1) hn τ) i =
      P.sphericalEndpoint (by omega) (hS.face τ i) :=
  P.sphericalFace_endpoint hn τ i

#print axioms exists_relative_spherical_straightening
#print axioms PartialSimplexStraightening.sphericalFace_endpoint

end Convexity.StdSimplex
