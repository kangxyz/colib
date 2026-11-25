/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeLevelEvaluation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! Evaluation of a whole-level relative-homotopy equality with abstract endpoints. -/
@[expose] public section
open CategoryTheory Topology
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
/-- Evaluate the same continuous-map equality before specializing the endpoint data. -/
theorem level_eq_apply {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K') (n : ℕ)
    (e : (J.level n).toContinuousMap = (J'.level n).toContinuousMap)
    (r s : unitInterval) (x : E.space n) :
    J.level n (r, (s, x)) = J'.level n (r, (s, x)) := DFunLike.congr_fun e _
end Topology.LoopPrespectrum.Homotopy.RelHomotopy

namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy

theorem ofLevels_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (ofLevels J H' K' hH hK).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl
end Topology.LoopPrespectrum.Homotopy.RelHomotopy
