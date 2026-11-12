/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopCounit

/-! # Naturality of the actual reduced suspension evaluation -/
@[expose] public noncomputable section
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum

/-- The actual counit commutes with every genuine spectrum map. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:78"
  "adaptation" "Original whole reduced-cone evaluation naturality."]
theorem suspensionLoopCounit_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    suspensionConeMap (parameterLoopingMap f) ≫ suspensionLoopCounit F =
      suspensionLoopCounit E ≫ f := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro x
    exact (f.map_point n).symm
  · intro z
    rfl

end Topology.LoopPrespectrum
