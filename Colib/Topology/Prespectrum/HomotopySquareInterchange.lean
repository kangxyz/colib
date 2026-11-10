/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopySquare

/-! Actual composition of two homotopies gives a full independent-parameter moving square. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopySquareInterchange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.Square

/-- Compose two actual homotopies without identifying either parameter or the structure time. -/
def interchange {E F G : LoopPrespectrum.{u}} {u v : E ⟶ F} {a b : F ⟶ G}
    (K : Homotopy u v) (N : Homotopy a b) :
    (Homotopy.precomp u N).Square (Homotopy.precomp v N) (K.postcomp a) (K.postcomp b) where
  level n := ⟨fun z ↦ N.level n (z.2.1, K.level n (z.1, z.2.2)), by fun_prop⟩
  at_zero n s x := by change N.level n (s, K.level n (0, x)) = _; rw [K.at_zero]; rfl
  at_one n s x := by change N.level n (s, K.level n (1, x)) = _; rw [K.at_one]; rfl
  left n r x := N.at_zero n (K.level n (r, x))
  right n r x := N.at_one n (K.level n (r, x))
  at_point n r s := by
    change N.level n (s, K.level n (r, E.point n)) = _
    rw [K.at_point, N.at_point]
  comm n r s x t := by
    change N.level (n + 1) (s, K.level (n + 1) (r, E.structureMap n x t)) =
      G.structureMap n (N.level n (s, K.level n (r, x))) t
    rw [K.comm, N.comm]

/-- Every coordinate of the moving square is the original iterated homotopy evaluation. -/
theorem interchange_apply {E F G : LoopPrespectrum.{u}} {u v : E ⟶ F} {a b : F ⟶ G}
    (K : Homotopy u v) (N : Homotopy a b) (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (interchange K N).level n (r, (s, x)) = N.level n (s, K.level n (r, x)) := rfl

end Topology.LoopPrespectrum.Homotopy.Square

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/HomotopySquareInterchange.lean:18-39"
  "adaptation" "Actual independent-parameter square from two original homotopies"]
  Topology.LoopPrespectrum.Homotopy.Square.interchange
