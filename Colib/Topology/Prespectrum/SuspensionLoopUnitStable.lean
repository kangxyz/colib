/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopUnit
public import Colib.Topology.Prespectrum.SuspensionLoopCounitStable

/-! # The original suspension unit at parameter loops

The original unit-counit triangle and the stable parameter-loop counit prove stability
of the unchanged suspension unit.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace Topology.LoopPrespectrum

/-- Stability of the actual counit implies stability of the unit at parameter loops. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopUnit.lean:69"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem suspensionLoopUnit_parameterLooping_isStableEquivalence
    (E : LoopPrespectrum.{u}) (hE : IsStableEquivalence (suspensionLoopCounit E)) :
    IsStableEquivalence (suspensionLoopUnit (parameterLooping E)) := by
  intro d
  let :=  parameterLooping_suspensionLoopCounit_isStableEquivalence E hE d
  have h := congrArg ((stableHomotopyFunctor d).map) (suspensionLoopUnit_counit E)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
  rw [IsIso.eq_inv_of_inv_hom_id h]
  infer_instance

end Topology.LoopPrespectrum
