/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.Homotopy

/-! # Composition of the actual zero spectrum map

The original zero-map identity needed by whole-null refinement.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}}

/-- Postcomposition preserves the original point-valued zero map. -/
@[simp, colib_ref "quillen" "Quillen/Topology/Prespectrum/FiberHomotopySquare.lean:32"
  "adaptation" "Original zero-map identity by actual basedness"]
theorem zeroHom_comp (f : F ⟶ G) : zeroHom E F ≫ f = zeroHom E G := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact f.map_point n

end Topology.LoopPrespectrum
