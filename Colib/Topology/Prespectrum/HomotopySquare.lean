/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.Homotopy

/-! # Continuous squares of coherent prespectrum homotopies

A square retains four specified boundary tracks, its whole basepoint line, and the independent
prespectrum structure coordinate. The two homotopy coordinates need not have fixed endpoints.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopySquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- A whole continuous square with four specified coherent boundary homotopies. -/
@[ext] structure Homotopy.Square {E F : LoopPrespectrum.{u}}
    {f₀₀ f₀₁ f₁₀ f₁₁ : E ⟶ F}
    (H₀ : Homotopy f₀₀ f₀₁) (H₁ : Homotopy f₁₀ f₁₁)
    (L : Homotopy f₀₀ f₁₀) (M : Homotopy f₀₁ f₁₁) where
  /-- The actual two-parameter continuous level map. -/
  level (n : ℕ) : C(unitInterval × (unitInterval × E.space n), F.space n)
  at_zero (n : ℕ) (s : unitInterval) (x : E.space n) : level n (0, (s, x)) = H₀.level n (s, x)
  at_one (n : ℕ) (s : unitInterval) (x : E.space n) : level n (1, (s, x)) = H₁.level n (s, x)
  left (n : ℕ) (r : unitInterval) (x : E.space n) : level n (r, (0, x)) = L.level n (r, x)
  right (n : ℕ) (r : unitInterval) (x : E.space n) : level n (r, (1, x)) = M.level n (r, x)
  at_point (n : ℕ) (r s : unitInterval) : level n (r, (s, E.point n)) = F.point n
  /-- Neither homotopy parameter is identified with the original structure time. -/
  comm (n : ℕ) (r s : unitInterval) (x : E.space n) (t : unitInterval) :
    level (n + 1) (r, (s, E.structureMap n x t)) =
      F.structureMap n (level n (r, (s, x))) t

namespace Homotopy.Square
variable {E F : LoopPrespectrum.{u}} {f₀₀ f₀₁ f₁₀ f₁₁ : E ⟶ F}
  {H₀ : Homotopy f₀₀ f₀₁} {H₁ : Homotopy f₁₀ f₁₁}
  {L : Homotopy f₀₀ f₁₀} {M : Homotopy f₀₁ f₁₁}

/-- Each comparison-time slice retains its actual moving endpoints. -/
def «at» (S : H₀.Square H₁ L M) (r : unitInterval) : Homotopy (L.at r) (M.at r) where
  level n := ⟨fun z ↦ S.level n (r, z), by fun_prop⟩
  at_zero n x := S.left n r x
  at_one n x := S.right n r x
  at_point n s := S.at_point n r s
  comm n s x t := S.comm n r s x t

/-- Every original track has its genuine constant square with fixed endpoint tracks. -/
def refl {f g : E ⟶ F} (H : Homotopy f g) :
    H.Square H (Homotopy.refl f) (Homotopy.refl g) where
  level n := ⟨fun z ↦ H.level n z.2, by fun_prop⟩
  at_zero _ _ _ := rfl
  at_one _ _ _ := rfl
  left n _r x := H.at_zero n x
  right n _r x := H.at_one n x
  at_point n _r s := H.at_point n s
  comm n _r s x t := H.comm n s x t

end Homotopy.Square
end Topology.LoopPrespectrum

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/HomotopySquare.lean:24-60"
  "adaptation" "Whole four-boundary square with independent comparison, \
    track and structure coordinates"]
  Topology.LoopPrespectrum.Homotopy.Square
