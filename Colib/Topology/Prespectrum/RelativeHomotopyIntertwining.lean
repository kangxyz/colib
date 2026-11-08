/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopyPasting

/-! Pasting and conjugation for actual endpoint-relative intertwining comparisons. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopyIntertwining.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology CategoryTheory.Functor
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy

/-- Two original commuting composition routes intertwine their transported endomorphism tracks. -/
def intertwine {E F : LoopPrespectrum.{u}} {a b c : E ⟶ F}
    (C : Homotopy a b) (D : Homotopy a c) (U : Homotopy a a)
    (V : Homotopy b b) (W : Homotopy c c)
    (JC : (C.trans V).RelHomotopy (U.trans C))
    (JD : (D.trans W).RelHomotopy (U.trans D)) :
    (V.trans (C.symm.trans D)).RelHomotopy ((C.symm.trans D).trans W) := by
  exact (Homotopy.RelHomotopy.transAssoc V C.symm D).symm.trans
    ((((Homotopy.RelHomotopy.rotate JC).symm).hcomp (Homotopy.RelHomotopy.refl D)).trans
      ((Homotopy.RelHomotopy.transAssoc C.symm U D).trans
        (((Homotopy.RelHomotopy.refl C.symm).hcomp JD.symm).trans
          (Homotopy.RelHomotopy.transAssoc C.symm D W).symm)))

/-- A proved intertwining comparison gives the literal three-sided conjugation boundary. -/
def conjugateBoundary {E F : LoopPrespectrum.{u}} {a b : E ⟶ F}
    (C : Homotopy a b) (U : Homotopy a a) (V : Homotopy b b)
    (J : (U.trans C).RelHomotopy (C.trans V)) :
    U.RelHomotopy ((C.trans V).trans C.symm) :=
  (transRefl U).symm.trans
    (((refl U).hcomp (reflTransSymm C)).trans
      ((transAssoc U C C.symm).symm.trans (J.hcomp (refl C.symm))))

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

-- COL-0324 references
attribute [colib_ref "quillen"
  "Prespectrum/RelativeHomotopyIntertwining.lean:1-39"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.intertwine
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.conjugateBoundary
