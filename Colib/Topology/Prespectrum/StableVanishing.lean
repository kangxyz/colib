/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableHomotopy
public import Mathlib.Algebra.Category.Grp.AB

/-!
Source: `Quillen/Topology/Prespectrum/StableVanishing.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Vanishing from the original signed stable stages

Every class in the original signed stable colimit comes from an actual stage. Vanishing of
those unchanged stage groups therefore implies vanishing without an Omega-spectrum assumption.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum

/-- Vanishing of every original signed stage forces the actual stable group to vanish. -/
theorem stableHomotopyGroup_subsingleton_of_stages
    (E : LoopPrespectrum.{u}) (d : ℤ)
    (hstage : ∀ n, Subsingleton ((stableSystem E d).obj n)) :
    Subsingleton (stableHomotopyGroup E d) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hz (a : stableHomotopyGroup E d) : a = 0 := by
    obtain ⟨n, a, rfl⟩ := Concrete.colimit_exists_rep (stableSystem E d) a
    rw [(hstage n).elim a 0]
    exact map_zero _
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Topology.LoopPrespectrum
