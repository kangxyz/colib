module

public import Colib.Topology.Realization.FiniteSimplexStraightening

open Convexity
open scoped Topology unitInterval

namespace Convexity.StdSimplex

universe u

variable {Z : Type u} [TopologicalSpace Z]

example [PathConnectedSpace Z] (n N : ℕ) (z : Z) (S F : FiniteSimplexFamily Z)
    (hS : S.FaceClosed) (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    ∃ P : PartialSimplexStraightening n z S F hS N,
      (∀ d (s : {s // s ∈ S d}), s.val ∈ F d →
        ∀ x t, P.track d s (x, t) = s.val x) ∧
      (∀ d, d + 1 < N → ∀ (s : {s // s ∈ S (d + 1)}) i x t,
        P.track (d + 1) s (map i.succAbove x, t) = P.track d (hS.face s i) (x, t)) ∧
      (∀ d, d < N → d < n → ∀ s x, P.track d s (x, 1) = z) := by
  obtain ⟨P⟩ :=
    exists_finite_simplex_straightening_of_pathConnected n N z S F hS hF hs hcollapsed
  exact ⟨P, P.stationary, P.face, P.top⟩

#print axioms exists_finite_simplex_straightening_of_pathConnected

end Convexity.StdSimplex
