/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Exact pointwise terminal-pause evaluation

The original endpoint transport is retained and reduced only after taking its whole level.
Comparison time, path time and the original source point are independent. No carrier evaluator
or actual J0 comparison is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- Whole-level endpoint casts preserve all comparison and path coordinates literally. -/
theorem Homotopy.RelHomotopy.ofLevels_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.ofLevels H' K' hH hK).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl

end Topology.LoopPrespectrum
