/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopCounit
public import Colib.Topology.Prespectrum.HomotopyLoop

/-! # The original actual successor, counit and backward triangle

Only the selected original construction and exact triangle are migrated here.
No stability, connectivity or telescope comparison is assumed or claimed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Topology.LoopPrespectrum
/-- The original forward cone contraction, with both endpoints the actual zero map. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopUnit.lean:29"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def suspensionCylinderHomotopy (E : LoopPrespectrum.{u}) :
    Homotopy (zeroHom E (suspensionCone E)) (zeroHom E (suspensionCone E)) :=
  mappingConeHomotopy (zeroHom E pointPrespectrum)

/-- The suspension-loop unit retains the original cone time in its forward order. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopUnit.lean:34"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def suspensionLoopUnit (E : LoopPrespectrum.{u}) : E ⟶ parameterLooping (suspensionCone E) :=
  (suspensionCylinderHomotopy E).zeroLoopMap

/-- The triangle evaluates at the same original loop time, without reversal or transpose. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopUnit.lean:57"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
theorem suspensionLoopUnit_counit (E : LoopPrespectrum.{u}) :
    suspensionLoopUnit (parameterLooping E) ≫
      parameterLoopingMap (suspensionLoopCounit E) = 𝟙 (parameterLooping E) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext s
  rfl

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0553"]
  Topology.LoopPrespectrum.suspensionLoopUnit

attribute [colib_tag "COL-0553"]
  Topology.LoopPrespectrum.suspensionLoopUnit_counit
