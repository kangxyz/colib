/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.RelativeHomotopy

/-! Transport the endpoint arrows of actual homotopies without changing any full level track. -/

/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopyTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Change only the endpoint-arrow witnesses; every whole level track stays literally unchanged. -/
def Homotopy.cast {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    (H : Homotopy f g) (hf : f = f') (hg : g = g') : Homotopy f' g' where
  level := H.level
  at_zero n x := (H.at_zero n x).trans (congrArg (fun a ↦ a.map n x) hf)
  at_one n x := (H.at_one n x).trans (congrArg (fun a ↦ a.map n x) hg)
  at_point := H.at_point
  comm := H.comm

/-- Endpoint transport preserves the original continuous two-parameter comparison. -/
def Homotopy.RelHomotopy.cast {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H K : Homotopy f g} (J : H.RelHomotopy K) (hf : f = f') (hg : g = g') :
    (H.cast hf hg).RelHomotopy (K.cast hf hg) where
  level := J.level
  comm := J.comm

/-- An endpoint transport changes no continuous level. -/
theorem Homotopy.cast_level {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    (H : Homotopy f g) (hf : f = f') (hg : g = g') (n : ℕ) :
    (H.cast hf hg).level n = H.level n := rfl

end Topology.LoopPrespectrum
