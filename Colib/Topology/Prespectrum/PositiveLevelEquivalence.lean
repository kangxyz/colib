/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableEquivalence

/-!
# Stable equivalence from actual positive-level maps

The chosen stable systems only use levels at least two. Complete weak equivalence on the original
positive levels therefore suffices, without imposing a condition on level zero or an Omega axiom.
-/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum

/-- Weakness of the unchanged positive-level maps already gives a stable equivalence. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PositiveLevelEquivalence.lean:26"
  "adaptation" "Original positive-level stable-system proof; no condition on level zero."]
theorem isStableEquivalence_of_positiveLevel {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : ∀ n, IsWeakHomotopyEquivalence (f.map (n + 1))) : IsStableEquivalence f := by
  intro d
  have hstage (n : ℕ) : IsIso ((stableSystemMap f d).app n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb {y : F.space ((-d).toNat + n + 2)}
        (h : f.map ((-d).toNat + n + 2) (E.point ((-d).toNat + n + 2)) = y) :
        Function.Bijective (HomotopyGroup.map (N := Fin (d.toNat + n + 2))
          (f.map ((-d).toNat + n + 2)) h) := by
      cases h
      exact (hf ((-d).toNat + n + 1)).homotopy_bijective
        (E.point ((-d).toNat + n + 2)) (d.toNat + n + 2)
    exact hb (f.map_point ((-d).toNat + n + 2))
  let : ∀ n, IsIso ((stableSystemMap f d).app n) := hstage
  let : IsIso (stableSystemMap f d) := NatIso.isIso_of_isIso_app _
  change IsIso (colim.map (stableSystemMap f d))
  infer_instance

end Topology.LoopPrespectrum
