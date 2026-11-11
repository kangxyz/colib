/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Homotopy

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
/-- The actual singleton prespectrum, with literal constant based structure loops. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/Point.lean:27"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def pointPrespectrum : LoopPrespectrum.{u} where
  space _ := TopCat.of PUnit.{u + 1}
  point _ := PUnit.unit
  structureMap _ := ContinuousMap.const _ (Path.refl PUnit.unit)
  map_point _ := rfl

end Topology.LoopPrespectrum
