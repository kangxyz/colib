/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.StableConnectivity

/-!
# Stable equivalence from an eventual finite range at the original chosen points

Only the positive homotopy groups at the actual chosen points enter the original signed
stable systems. An eventual slope-two bijectivity range for those maps therefore suffices;
no connectivity assertion at arbitrary homotopy-fiber points is required. The arrow and
both prespectrum structures remain unchanged.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/StableFiniteRange.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum

/-- Eventual finite bijectivity at the actual chosen points gives an original stable equivalence.
-/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/StableFiniteRange.lean:26"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem isStableEquivalence_of_eventually_linearPi {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (N c : ℕ) (hf : ∀ n, N ≤ n → ∀ k, k + 2 < 2 * n - c →
      Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
        (f.map (n + 1)) (f.map_point (n + 1)))) : IsStableEquivalence f := by
  intro d
  change IsIso (colimMap (stableSystemMap f d))
  apply CategoryTheory.Limits.SequentialSystem.isIso_colimMap_of_eventually
    (stableSystemMap f d) (N + d.toNat + c + 1)
  intro n hn
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact hf ((-d).toNat + n + 1) (by omega) (d.toNat + n) (by omega)

end Topology.LoopPrespectrum
