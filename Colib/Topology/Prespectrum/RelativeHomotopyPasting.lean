/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-! Rotate an actual two-route comparison to the boundary orientation used in Bass squares. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopyPasting.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology CategoryTheory.Functor
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {a b c d : E ⟶ F}

/-- Rotate a proved whole two-route comparison by explicit cancellation of its original tracks.
The comparison is relative to the new endpoints and preserves the independent structure time. -/
def rotate {H : Homotopy a b} {K : Homotopy b d} {L : Homotopy a c}
    {M : Homotopy c d} (J : (H.trans K).RelHomotopy (L.trans M)) :
    (H.symm.trans L).RelHomotopy (K.trans M.symm) := by
  have j1 := (refl H.symm).hcomp (transRefl L).symm
  have j2 := (refl H.symm).hcomp ((refl L).hcomp (reflTransSymm M))
  have j3 := (refl H.symm).hcomp (transAssoc L M M.symm).symm
  have j4 := (refl H.symm).hcomp (J.symm.hcomp (refl M.symm))
  have j5 := (transAssoc H.symm (H.trans K) M.symm).symm
  have j6 := ((transAssoc H.symm H K).symm).hcomp (refl M.symm)
  have j7 := ((reflSymmTrans H).symm.hcomp (refl K)).hcomp (refl M.symm)
  have j8 := (reflTrans K).hcomp (refl M.symm)
  exact j1.trans (j2.trans (j3.trans (j4.trans (j5.trans (j6.trans (j7.trans j8))))))

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

-- COL-0324 references
attribute [colib_ref "quillen"
  "Prespectrum/RelativeHomotopyPasting.lean:1-33"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.rotate
