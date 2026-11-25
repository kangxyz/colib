/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyPasting
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting

/-!
# A whole square from two original comparisons with a common prefix

The common prefix is removed by the original relative path contractions. All four boundary
tracks retain their actual parametrizations, including the split reverse-forward upper edge.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {V W : LoopPrespectrum.{u}} {o a b c d e : V ⟶ W}
  {C : Homotopy o a} {D : Homotopy a d} {F : Homotopy a e}
  {L : Homotopy o b} {P : Homotopy b d} {T : Homotopy o c} {M : Homotopy c e}

/-- Preserve the original boundary word while cancelling its common comparison prefix. -/
def commonPrefixPasting
    (J : (C.trans D).RelHomotopy (L.trans P))
    (K : (C.trans F).RelHomotopy (T.trans M)) :
    T.RelHomotopy ((L.trans (P.trans (D.symm.trans F))).trans M.symm) := by
  have start : T.RelHomotopy ((T.trans M).trans M.symm) :=
    (transRefl T).symm.trans
      (((refl T).hcomp (reflTransSymm M)).trans (transAssoc T M M.symm).symm)
  have insert : (C.trans F).RelHomotopy ((C.trans D).trans (D.symm.trans F)) :=
    ((refl C).hcomp (reflTrans F).symm).trans
      (((refl C).hcomp ((reflTransSymm D).hcomp (refl F))).trans
        (((refl C).hcomp (transAssoc D D.symm F)).trans
          (transAssoc C D (D.symm.trans F)).symm))
  exact start.trans ((K.symm.hcomp (refl M.symm)).trans
    ((insert.hcomp (refl M.symm)).trans
      (((J.hcomp (refl (D.symm.trans F))).hcomp (refl M.symm)).trans
        ((transAssoc L P (D.symm.trans F)).hcomp (refl M.symm)))))

/-- The square retains all four original boundary tracks at every spectrum level. -/
def commonPrefixSquare
    (J : (C.trans D).RelHomotopy (L.trans P))
    (K : (C.trans F).RelHomotopy (T.trans M)) :
    T.Square (P.trans (D.symm.trans F)) L M :=
  (commonPrefixPasting J K).toSquare

end Topology.LoopPrespectrum.Homotopy.RelHomotopy
