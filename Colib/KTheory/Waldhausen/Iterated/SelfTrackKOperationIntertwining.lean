/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperation
public import Colib.Topology.Prespectrum.SelfTrackIntertwining

/-! # Actual intertwining transports original nonnegative K-group operations -/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/SelfTrackKOperationIntertwining.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D)
variable {f g : originalPrespectrum W ⟶ originalPrespectrum V}

/-- A supplied whole intertwining identifies the actual homomorphisms on every original K-group. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationIntertwining.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_intertwine
    (H : Homotopy f f) (K : Homotopy g g) (T : Homotopy f g)
    (J : (H.trans T).RelHomotopy (T.trans K)) (n : ℕ) :
    originalKSelfTrackOperation W V H n = originalKSelfTrackOperation W V K n := by
  apply originalKSelfTrackOperation_unique W V K n
  intro a
  rw [originalKSelfTrackOperation_stable, H.stableOperation_intertwine K T J]

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0321"]
  CategoryTheory.Waldhausen.IteratedS.originalKSelfTrackOperation_intertwine
