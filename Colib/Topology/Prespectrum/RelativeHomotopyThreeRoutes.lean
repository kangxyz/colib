/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyPasting

/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopyThreeRoutes.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! The three-route cancellation used to compose actual coefficient-map squares. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {o a b c d e f z : E ⟶ F}

/-- Paste the three original associativity comparisons around a two-square coefficient diagram.
All inverses are the actual reversed tracks, and every reassociation is an explicit relative
comparison, preserving the original maps and independent structure coordinate. -/
def threeRoutes {C : Homotopy o a} {D : Homotopy a b} {E' : Homotopy o c}
    {F' : Homotopy c b} {G : Homotopy o d} {H : Homotopy d e} {I : Homotopy c e}
    {J : Homotopy o f} {K : Homotopy f z} {L : Homotopy d z}
    (j1 : (C.trans D).RelHomotopy (E'.trans F'))
    (j2 : (G.trans H).RelHomotopy (E'.trans I))
    (j3 : (G.trans L).RelHomotopy (J.trans K)) :
    ((F'.symm.trans I).trans (H.symm.trans L)).RelHomotopy
      (D.symm.trans ((C.symm.trans J).trans K)) := by
  have rotateMiddle : (I.trans H.symm).RelHomotopy (E'.symm.trans G) := by
    simpa only [Homotopy.symm_trans, Homotopy.symm_symm] using (rotate j2).symmPath.symm
  have reverseFirst : (F'.symm.trans E'.symm).RelHomotopy (D.symm.trans C.symm) := by
    simpa only [Homotopy.symm_trans] using j1.symmPath.symm
  exact ((transAssoc (F'.symm.trans I) H.symm L).symm.trans
    ((transAssoc F'.symm I H.symm).hcomp (refl L))).trans
    (((refl F'.symm).hcomp rotateMiddle).hcomp (refl L) |>.trans
      (((transAssoc F'.symm E'.symm G).symm.hcomp (refl L)).trans
        ((transAssoc (F'.symm.trans E'.symm) G L).trans
          ((reverseFirst.hcomp j3).trans
            ((transAssoc D.symm C.symm (J.trans K)).trans
              ((refl D.symm).hcomp (transAssoc C.symm J K).symm))))))

end Topology.LoopPrespectrum.Homotopy.RelHomotopy
