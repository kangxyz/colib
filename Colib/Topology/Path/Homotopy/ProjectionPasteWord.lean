/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-! The literal scalar word of the original two-projection-square pasting.
Adapted from `Quillen/Topology/Path/ProjectionPasteWord.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Path.Homotopy
variable {X : Type u} [TopologicalSpace X]

/-- The exact initial straightening word from the native pasteTwoSquares definition. -/
def projectionStraighten {x y z w : X} {D : Path x y} {A : Path y w}
    {T : Path x z} {K : Path z w} (J : A.Homotopy (D.symm.trans (T.trans K))) :
    (D.trans A).Homotopy (T.trans K) :=
  ((refl D).hcomp J).trans
    ((transAssoc D D.symm (T.trans K)).symm.trans
      (((reflTransSymm D).symm.hcomp (refl (T.trans K))).trans (reflTrans (T.trans K))))

variable {o a b c d e f m : X}
/-- Native rotations, actual outer-track cancellation and all original reassociations. -/
def pasteProjectionSquares {Dp : Path o a} {Dm : Path o b} {T : Path o m}
    {Lp : Path a c} {Pp : Path c d} {Kp : Path m d}
    {Lm : Path b e} {Pm : Path e f} {Km : Path m f}
    (Jp : (Lp.trans Pp).Homotopy (Dp.symm.trans (T.trans Kp)))
    (Jm : (Lm.trans Pm).Homotopy (Dm.symm.trans (T.trans Km))) :
    (Dp.symm.trans Dm).Homotopy
      ((Lp.trans (Pp.trans ((Kp.symm.trans Km).trans Pm.symm))).trans Lm.symm) := by
  have first := rotate (projectionStraighten Jp)
  have second : (T.symm.trans Dm).Homotopy
      (Km.trans (Pm.symm.trans Lm.symm)) := by
    simpa only [Path.trans_symm, Path.symm_symm] using
      (rotate (projectionStraighten Jm)).symm₂
  have insert : (Dp.symm.trans Dm).Homotopy
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
end Path.Homotopy
