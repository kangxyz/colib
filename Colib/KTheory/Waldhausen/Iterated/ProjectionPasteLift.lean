/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.ScalarRectangleLiftOps
public import Colib.Topology.Path.Homotopy.ProjectionPasteWord
public import Colib.Topology.Prespectrum.RelativeHomotopySquarePasting

/-! Whole-level lifting of the literal original two-projection-square pasting word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
  (S : ModelSimplex V W k)

private theorem path_cast_apply {a b : StdSimplex ℝ (Fin (k + 1))}
    {p q p' q' : Path a b} (hp : p = p') (hq : q = q')
    (ht : p.Homotopy q = p'.Homotopy q') (J : p.Homotopy q) (r s : unitInterval) :
    (cast ht J) (r, s) = J (r, s) := by
  subst p'
  subst q'
  simp

private theorem rel_cast_apply {f g : prespectrum V ⟶ prespectrum W}
    {H K H' K' : Homotopy f g} (hH : H = H') (hK : K = K')
    (ht : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (cast ht J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst H'
  subst K'
  simp

/-- The literal straightening subword of `RelHomotopy.pasteTwoSquares`. -/
private def projectionStraightenNative {E F : LoopPrespectrum.{u}} {x y z w : E ⟶ F}
    {D : Homotopy x y} {A : Homotopy y w} {T : Homotopy x z} {K : Homotopy z w}
    (J : A.RelHomotopy (D.symm.trans (T.trans K))) : (D.trans A).RelHomotopy (T.trans K) :=
  ((Homotopy.RelHomotopy.refl D).hcomp J).trans
    ((Homotopy.RelHomotopy.transAssoc D D.symm (T.trans K)).symm.trans
      (((Homotopy.RelHomotopy.reflTransSymm D).symm.hcomp
        (Homotopy.RelHomotopy.refl (T.trans K))).trans
        (Homotopy.RelHomotopy.reflTrans (T.trans K))))

/-- Lifting of the original initial straightening, with its full cancellation parameter. -/
private theorem HomotopyLift.projectionStraighten
    {a b c d : StdSimplex ℝ (Fin (k + 1))}
    {f g h j : prespectrum V ⟶ prespectrum W}
    {pD : Path a b} {pA : Path b d} {pT : Path a c} {pK : Path c d}
    {hD : Homotopy f g} {hA : Homotopy g j} {hT : Homotopy f h} {hK : Homotopy h j}
    (lD : PathLift S pD hD) (lT : PathLift S pT hT) (lK : PathLift S pK hK)
    {J : pA.Homotopy (pD.symm.trans (pT.trans pK))}
    {N : hA.RelHomotopy (hD.symm.trans (hT.trans hK))} (lJ : HomotopyLift S J N) :
    HomotopyLift S (Path.Homotopy.projectionStraighten J)
      (projectionStraightenNative N) := by
  unfold Path.Homotopy.projectionStraighten projectionStraightenNative
  exact HomotopyLift.trans S (HomotopyLift.hcomp S (PathLift.refl S lD) lJ)
    (HomotopyLift.trans S
      (HomotopyLift.symm S (RectanglePathLift.transAssoc S lD
        (PathLift.symm S lD) (PathLift.trans S lT lK)))
      (HomotopyLift.trans S
        (HomotopyLift.hcomp S (HomotopyLift.symm S (PathLift.reflTransSymm S lD))
          (PathLift.refl S (PathLift.trans S lT lK)))
        (RectanglePathLift.reflTrans S (PathLift.trans S lT lK))))

variable {o a b c d e f m : StdSimplex ℝ (Fin (k + 1))}
variable {O A B C D E F M : prespectrum V ⟶ prespectrum W}
variable {pDp : Path o a} {pDm : Path o b} {pT : Path o m}
  {pLp : Path a c} {pPp : Path c d} {pKp : Path m d}
  {pLm : Path b e} {pPm : Path e f} {pKm : Path m f}
variable {hDp : Homotopy O A} {hDm : Homotopy O B} {hT : Homotopy O M}
  {hLp : Homotopy A C} {hPp : Homotopy C D} {hKp : Homotopy M D}
  {hLm : Homotopy B E} {hPm : Homotopy E F} {hKm : Homotopy M F}

/-- Every point of the original pasteTwoSquares word is evaluated by the scalar counterpart. -/
theorem HomotopyLift.pasteProjectionSquares
    (lDp : PathLift S pDp hDp) (lDm : PathLift S pDm hDm) (lT : PathLift S pT hT)
    (lLp : PathLift S pLp hLp) (lPp : PathLift S pPp hPp) (lKp : PathLift S pKp hKp)
    (lLm : PathLift S pLm hLm) (lPm : PathLift S pPm hPm) (lKm : PathLift S pKm hKm)
    {Jp : (pLp.trans pPp).Homotopy (pDp.symm.trans (pT.trans pKp))}
    {Jm : (pLm.trans pPm).Homotopy (pDm.symm.trans (pT.trans pKm))}
    {Np : (hLp.trans hPp).RelHomotopy (hDp.symm.trans (hT.trans hKp))}
    {Nm : (hLm.trans hPm).RelHomotopy (hDm.symm.trans (hT.trans hKm))}
    (lJp : HomotopyLift S Jp Np) (lJm : HomotopyLift S Jm Nm) :
    HomotopyLift S (Path.Homotopy.pasteProjectionSquares Jp Jm)
      (Homotopy.RelHomotopy.pasteTwoSquares Np Nm) := by
  unfold Path.Homotopy.pasteProjectionSquares Homotopy.RelHomotopy.pasteTwoSquares
  have first := HomotopyLift.rectangleRotate S lDp (PathLift.trans S lLp lPp) lT lKp
    (HomotopyLift.projectionStraighten S lDp lT lKp lJp)
  have second : HomotopyLift S
      (show (pT.symm.trans pDm).Homotopy (pKm.trans (pPm.symm.trans pLm.symm)) from by
        simpa only [Path.trans_symm, Path.symm_symm] using
          (Path.Homotopy.rotate (Path.Homotopy.projectionStraighten Jm)).symm₂)
      (show (hT.symm.trans hDm).RelHomotopy (hKm.trans (hPm.symm.trans hLm.symm)) from by
        simpa only [Homotopy.symm_trans, Homotopy.symm_symm] using
          (Homotopy.RelHomotopy.rotate
            (projectionStraightenNative Nm)).symmPath) := by
    intro n r s x
    have ep : (pDm.symm.trans pT).symm = pT.symm.trans pDm := by
      simp only [Path.trans_symm, Path.symm_symm]
    have eq : ((pLm.trans pPm).trans pKm.symm).symm =
        pKm.trans (pPm.symm.trans pLm.symm) := by simp only [Path.trans_symm, Path.symm_symm]
    have eH : (hDm.symm.trans hT).symm = hT.symm.trans hDm := by
      simp only [Homotopy.symm_trans, Homotopy.symm_symm]
    have eK : ((hLm.trans hPm).trans hKm.symm).symm =
        hKm.trans (hPm.symm.trans hLm.symm) := by
      simp only [Homotopy.symm_trans, Homotopy.symm_symm]
    simp only [eq_mp_eq_cast, path_cast_apply ep eq, rel_cast_apply eH eK]
    exact (HomotopyLift.symmPath S
      (HomotopyLift.rectangleRotate S lDm (PathLift.trans S lLm lPm) lT lKm
        (HomotopyLift.projectionStraighten S lDm lT lKm lJm))) n r s x
  have insert0 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S lDp))
    (HomotopyLift.symm S (RectanglePathLift.reflTrans S lDm))
  have insert1 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S lDp))
    (HomotopyLift.hcomp S (PathLift.reflTransSymm S lT) (PathLift.refl S lDm))
  have insert2 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S lDp))
    (RectanglePathLift.transAssoc S lT (PathLift.symm S lT) lDm)
  have insert3 := HomotopyLift.symm S (RectanglePathLift.transAssoc S
    (PathLift.symm S lDp) lT (PathLift.trans S (PathLift.symm S lT) lDm))
  have ins := HomotopyLift.trans S insert0
    (HomotopyLift.trans S insert1 (HomotopyLift.trans S insert2 insert3))
  have tail1 := RectanglePathLift.transAssoc S (PathLift.trans S lLp lPp)
    (PathLift.symm S lKp) (PathLift.trans S lKm
      (PathLift.trans S (PathLift.symm S lPm) (PathLift.symm S lLm)))
  have tail2 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.trans S lLp lPp))
    (HomotopyLift.symm S (RectanglePathLift.transAssoc S (PathLift.symm S lKp) lKm
      (PathLift.trans S (PathLift.symm S lPm) (PathLift.symm S lLm))))
  have tail3 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.trans S lLp lPp))
    (HomotopyLift.symm S (RectanglePathLift.transAssoc S
      (PathLift.trans S (PathLift.symm S lKp) lKm) (PathLift.symm S lPm) (PathLift.symm S lLm)))
  have tail4 := HomotopyLift.symm S (RectanglePathLift.transAssoc S (PathLift.trans S lLp lPp)
    (PathLift.trans S (PathLift.trans S (PathLift.symm S lKp) lKm) (PathLift.symm S lPm))
    (PathLift.symm S lLm))
  have tail5 := HomotopyLift.hcomp S
    (RectanglePathLift.transAssoc S lLp lPp
      (PathLift.trans S (PathLift.trans S (PathLift.symm S lKp) lKm) (PathLift.symm S lPm)))
    (PathLift.refl S (PathLift.symm S lLm))
  exact HomotopyLift.trans S (HomotopyLift.trans S ins (HomotopyLift.hcomp S first second))
    (HomotopyLift.trans S tail1 (HomotopyLift.trans S tail2
      (HomotopyLift.trans S tail3 (HomotopyLift.trans S tail4 tail5))))

end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
