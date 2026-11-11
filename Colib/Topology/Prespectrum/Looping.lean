/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Homotopy
public import Colib.Util.References

/-!
# Actual looping and the original stabilization map

Levelwise loops carry the looped original structure maps and form an actual endofunctor.
The original adjoint structure maps give a genuine map to the looped tail. No stable
localization or Omega replacement is asserted here.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- Actual levelwise loop spaces with looped original structure maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/Looping.lean:29"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def looping (E : LoopPrespectrum.{u}) : LoopPrespectrum.{u} where
  space n := TopCat.of (Path (E.point n) (E.point n))
  point n := Path.refl (E.point n)
  structureMap n := basedLoopMap (E.structureMap n) (E.map_point n)
  map_point n := basedLoopMap_refl (E.structureMap n) (E.map_point n)

/-- A genuine based map induces a genuine map of the levelwise loop prespectra. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/Looping.lean:36"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def loopingMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) : looping E ⟶ looping F where
  map n := basedLoopMap (f.map n) (f.map_point n)
  map_point n := basedLoopMap_refl (f.map n) (f.map_point n)
  comm n γ := by
    change Path (E.point n) (E.point n) at γ
    apply Path.ext
    funext s
    apply Path.ext
    funext t
    exact congrArg (fun p ↦ p t) (f.comm n (γ s))

/-- Actual looping is functorial before imposing any stable equivalences. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/Looping.lean:48"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def loopingFunctor : LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} where
  obj := looping
  map := loopingMap
  map_id E := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext t
    rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext t
    rfl

/-- Drop the zeroth level, retaining the actual structure maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/Looping.lean:69"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def tail (E : LoopPrespectrum.{u}) : LoopPrespectrum.{u} where
  space n := E.space (n+1)
  point n := E.point (n+1)
  structureMap n := E.structureMap (n+1)
  map_point n := E.map_point (n+1)

/-- The original adjoint structure maps assemble into their canonical stabilization map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/Looping.lean:76"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def stabilizationMap (E : LoopPrespectrum.{u}) : E ⟶ looping (tail E) where
  map n := E.structureMap n
  map_point n := E.map_point n
  comm _n _x := rfl

end Topology.LoopPrespectrum
