/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopyPasting

/-! Cancel the common outer track in two genuine coefficient-square comparisons. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopySquarePasting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {o a b c d e f m : E ⟶ F}

/-- Two proved chart pastings give the exact boundary-pasted track, with explicit association.
The middle outer track is canceled by its actual parameter contraction; all three independent
comparison, original-path, and structure coordinates are retained. -/
def pasteTwoSquares {Dp : Homotopy o a} {Dm : Homotopy o b} {T : Homotopy o m}
    {Lp : Homotopy a c} {Pp : Homotopy c d} {Kp : Homotopy m d}
    {Lm : Homotopy b e} {Pm : Homotopy e f} {Km : Homotopy m f}
    (Jp : (Lp.trans Pp).RelHomotopy (Dp.symm.trans (T.trans Kp)))
    (Jm : (Lm.trans Pm).RelHomotopy (Dm.symm.trans (T.trans Km))) :
    (Dp.symm.trans Dm).RelHomotopy
      ((Lp.trans (Pp.trans ((Kp.symm.trans Km).trans Pm.symm))).trans Lm.symm) := by
  let straighten {x y z w : E ⟶ F} {D : Homotopy x y} {A : Homotopy y w}
      {T' : Homotopy x z} {K : Homotopy z w}
      (J : A.RelHomotopy (D.symm.trans (T'.trans K))) :
      (D.trans A).RelHomotopy (T'.trans K) :=
    ((refl D).hcomp J).trans
      ((transAssoc D D.symm (T'.trans K)).symm.trans
        (((reflTransSymm D).symm.hcomp (refl (T'.trans K))).trans (reflTrans (T'.trans K))))
  have first := rotate (straighten Jp)
  have second : (T.symm.trans Dm).RelHomotopy
      (Km.trans (Pm.symm.trans Lm.symm)) := by
    simpa only [Homotopy.symm_trans, Homotopy.symm_symm] using
      (rotate (straighten Jm)).symmPath
  have insert : (Dp.symm.trans Dm).RelHomotopy
      ((Dp.symm.trans T).trans (T.symm.trans Dm)) :=
    ((refl Dp.symm).hcomp (reflTrans Dm).symm).trans
      (((refl Dp.symm).hcomp ((reflTransSymm T).hcomp (refl Dm))).trans
        (((refl Dp.symm).hcomp (transAssoc T T.symm Dm)).trans
          (transAssoc Dp.symm T (T.symm.trans Dm)).symm))
  exact (insert.trans (first.hcomp second)).trans
    ((transAssoc (Lp.trans Pp) Kp.symm (Km.trans (Pm.symm.trans Lm.symm))).trans
      (((refl (Lp.trans Pp)).hcomp
        (transAssoc Kp.symm Km (Pm.symm.trans Lm.symm)).symm).trans
        (((refl (Lp.trans Pp)).hcomp
          (transAssoc (Kp.symm.trans Km) Pm.symm Lm.symm).symm).trans
          ((transAssoc (Lp.trans Pp) ((Kp.symm.trans Km).trans Pm.symm) Lm.symm).symm.trans
            ((transAssoc Lp Pp ((Kp.symm.trans Km).trans Pm.symm)).hcomp (refl Lm.symm))))))

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RelativeHomotopySquarePasting.lean:21-53"
  "adaptation" "Two proved chart fillers with actual cancellation of their common outer track"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.pasteTwoSquares
