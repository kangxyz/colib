/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Source-object transport of entire prespectrum homotopies

Equality elimination transports the complete continuous maps, not merely their endpoints.
The source equality is retained until the two presentations have been identified.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Precomposition respects source-object transport and whole-level equality. -/
theorem Homotopy.precomp_level_congr_source
    {D D' E F : LoopPrespectrum.{u}} (eD : D = D')
    {a b a' b' : E ⟶ F}
    (h : D ⟶ E) (h' : D' ⟶ E) (hh : HEq h h')
    (H : Homotopy a b) (K : Homotopy a' b') (n : ℕ)
    (hHK : H.level n = K.level n) :
    HEq ((Homotopy.precomp h H).level n)
      ((Homotopy.precomp h' K).level n) := by
  subst D'
  have eh : h = h' := eq_of_heq hh
  subst h'
  exact heq_of_eq (Homotopy.precomp_level_congr h H K n hHK)

/-- Postcomposition respects source-object transport and whole-level equality. -/
theorem Homotopy.postcomp_level_congr_source
    {D D' E F : LoopPrespectrum.{u}} (eD : D = D')
    {a b : D ⟶ E} {a' b' : D' ⟶ E}
    (H : Homotopy a b) (K : Homotopy a' b')
    (h : E ⟶ F) (n : ℕ)
    (hHK : HEq (H.level n) (K.level n)) :
    HEq ((H.postcomp h).level n) ((K.postcomp h).level n) := by
  subst D'
  exact heq_of_eq (Homotopy.postcomp_level_congr H K h n (eq_of_heq hHK))

end Topology.LoopPrespectrum
