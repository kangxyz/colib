/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.ThreeRoutes
public import Colib.KTheory.Waldhausen.Iterated.ScalarReassociationLifts
public import Colib.Topology.Prespectrum.RelativeHomotopyThreeRoutes

/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ScalarRectangleLiftOps.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! Whole-level compatibility of the scalar rotation and full three-route word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
  (S : ModelSimplex V W k)
variable {a b c d : StdSimplex ℝ (Fin (k + 1))}
variable {f g h z : prespectrum V ⟶ prespectrum W}
variable {P : Path a b} {Q : Path b d} {R : Path a c} {T : Path c d}
variable {H : Homotopy f g} {K : Homotopy g z}
variable {L : Homotopy f h} {M : Homotopy h z}

theorem HomotopyLift.rectangleRotate (hP : PathLift S P H) (hQ : PathLift S Q K)
    (hR : PathLift S R L) (hT : PathLift S T M)
    {J : (P.trans Q).Homotopy (R.trans T)}
    {N : (H.trans K).RelHomotopy (L.trans M)}
    (hJ : HomotopyLift S J N) :
    HomotopyLift S (Path.Homotopy.rotate J) (Homotopy.RelHomotopy.rotate N) := by
  unfold Path.Homotopy.rotate Homotopy.RelHomotopy.rotate
  exact (HomotopyLift.trans S
    (HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hP))
      (HomotopyLift.symm S (RectanglePathLift.transRefl S hR)))
    (HomotopyLift.trans S
      (HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hP))
        (HomotopyLift.hcomp S (PathLift.refl S hR)
          (PathLift.reflTransSymm S hT)))
      (HomotopyLift.trans S
        (HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hP))
          (HomotopyLift.symm S (RectanglePathLift.transAssoc S hR hT (PathLift.symm S hT))))
        (HomotopyLift.trans S
          (HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hP))
            (HomotopyLift.hcomp S (HomotopyLift.symm S hJ)
              (PathLift.refl S (PathLift.symm S hT))))
          (HomotopyLift.trans S
            (HomotopyLift.symm S
              (RectanglePathLift.transAssoc S (PathLift.symm S hP)
                (PathLift.trans S hP hQ) (PathLift.symm S hT)))
            (HomotopyLift.trans S
              (HomotopyLift.hcomp S
                (HomotopyLift.symm S
                  (RectanglePathLift.transAssoc S (PathLift.symm S hP) hP hQ))
                (PathLift.refl S (PathLift.symm S hT)))
              (HomotopyLift.trans S
                (HomotopyLift.hcomp S
                  (HomotopyLift.hcomp S
                    (HomotopyLift.symm S (RectanglePathLift.reflSymmTrans S hP))
                    (PathLift.refl S hQ))
                  (PathLift.refl S (PathLift.symm S hT)))
                (HomotopyLift.hcomp S (RectanglePathLift.reflTrans S hQ)
                  (PathLift.refl S (PathLift.symm S hT))))))))))
end CategoryTheory.Waldhausen.IteratedS.SimplexParameters

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
  (S : ModelSimplex V W k)
variable {o a b c d e f z : StdSimplex ℝ (Fin (k + 1))}
variable {O A B C D E F Z : prespectrum V ⟶ prespectrum W}
variable {pC : Path o a} {pD : Path a b} {pE : Path o c} {pF : Path c b}
variable {pG : Path o d} {pH : Path d e} {pI : Path c e}
variable {pJ : Path o f} {pK : Path f z} {pL : Path d z}
variable {hC : Homotopy O A} {hD : Homotopy A B}
variable {hE : Homotopy O C} {hF : Homotopy C B}
variable {hG : Homotopy O D} {hH : Homotopy D E} {hI : Homotopy C E}
variable {hJ : Homotopy O F} {hK : Homotopy F Z} {hL : Homotopy D Z}

private theorem path_cast_apply {x y : StdSimplex ℝ (Fin (k + 1))}
    {p q p' q' : Path x y} (hp : p = p') (hq : q = q')
    (ht : p.Homotopy q = p'.Homotopy q') (J : p.Homotopy q)
    (r s : unitInterval) : (cast ht J) (r, s) = J (r, s) := by
  subst p'
  subst q'
  simp

private theorem rel_cast_level_apply {f g : prespectrum V ⟶ prespectrum W}
    {H K H' K' : Homotopy f g} (hH : H = H') (hK : K = K')
    (ht : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (cast ht J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst H'
  subst K'
  simp

theorem HomotopyLift.threeRoutes
    (lC : PathLift S pC hC) (lD : PathLift S pD hD)
    (lE : PathLift S pE hE) (lF : PathLift S pF hF)
    (lG : PathLift S pG hG) (lH : PathLift S pH hH)
    (lI : PathLift S pI hI) (lJ : PathLift S pJ hJ)
    (lK : PathLift S pK hK) (lL : PathLift S pL hL)
    {j1 : (pC.trans pD).Homotopy (pE.trans pF)}
    {j2 : (pG.trans pH).Homotopy (pE.trans pI)}
    {j3 : (pG.trans pL).Homotopy (pJ.trans pK)}
    {n1 : (hC.trans hD).RelHomotopy (hE.trans hF)}
    {n2 : (hG.trans hH).RelHomotopy (hE.trans hI)}
    {n3 : (hG.trans hL).RelHomotopy (hJ.trans hK)}
    (lj1 : HomotopyLift S j1 n1) (lj2 : HomotopyLift S j2 n2)
    (lj3 : HomotopyLift S j3 n3) :
    HomotopyLift S (Path.Homotopy.threeRoutes j1 j2 j3)
      (Homotopy.RelHomotopy.threeRoutes n1 n2 n3) := by
  unfold Path.Homotopy.threeRoutes Homotopy.RelHomotopy.threeRoutes
  have rot : HomotopyLift S
      (show (pI.trans pH.symm).Homotopy (pE.symm.trans pG) from by
        simpa only [Path.trans_symm, Path.symm_symm] using
          (Path.Homotopy.rotate j2).symm₂.symm)
      (show (hI.trans hH.symm).RelHomotopy (hE.symm.trans hG) from by
        simpa only [Homotopy.symm_trans, Homotopy.symm_symm] using
          (Homotopy.RelHomotopy.rotate n2).symmPath.symm) := by
    intro n r s x
    have ep : (pH.trans pI.symm).symm = pI.trans pH.symm := by
      simp only [Path.trans_symm, Path.symm_symm]
    have eq : (pG.symm.trans pE).symm = pE.symm.trans pG := by
      simp only [Path.trans_symm, Path.symm_symm]
    have eH : (hH.trans hI.symm).symm = hI.trans hH.symm := by
      simp only [Homotopy.symm_trans, Homotopy.symm_symm]
    have eK : (hG.symm.trans hE).symm = hE.symm.trans hG := by
      simp only [Homotopy.symm_trans, Homotopy.symm_symm]
    simp only [eq_mp_eq_cast, path_cast_apply ep eq,
      rel_cast_level_apply eH eK]
    exact (HomotopyLift.symm S (HomotopyLift.symmPath S
      (HomotopyLift.rectangleRotate S lG lH lE lI lj2))) n r s x
  have rev : HomotopyLift S
      (show (pF.symm.trans pE.symm).Homotopy (pD.symm.trans pC.symm) from by
        simpa only [Path.trans_symm] using j1.symm₂.symm)
      (show (hF.symm.trans hE.symm).RelHomotopy (hD.symm.trans hC.symm) from by
        simpa only [Homotopy.symm_trans] using n1.symmPath.symm) := by
    intro n r s x
    have ep : (pE.trans pF).symm = pF.symm.trans pE.symm := by
      simp only [Path.trans_symm]
    have eq : (pC.trans pD).symm = pD.symm.trans pC.symm := by
      simp only [Path.trans_symm]
    have eH : (hE.trans hF).symm = hF.symm.trans hE.symm := by
      simp only [Homotopy.symm_trans]
    have eK : (hC.trans hD).symm = hD.symm.trans hC.symm := by
      simp only [Homotopy.symm_trans]
    simp only [eq_mp_eq_cast, path_cast_apply ep eq,
      rel_cast_level_apply eH eK]
    exact (HomotopyLift.symm S (HomotopyLift.symmPath S lj1)) n r s x
  have stepA := HomotopyLift.symm S (RectanglePathLift.transAssoc S
    (PathLift.trans S (PathLift.symm S lF) lI) (PathLift.symm S lH) lL)
  have stepB := HomotopyLift.hcomp S
    (RectanglePathLift.transAssoc S (PathLift.symm S lF) lI (PathLift.symm S lH))
    (PathLift.refl S lL)
  have stepC := HomotopyLift.hcomp S
    (HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S lF)) rot)
    (PathLift.refl S lL)
  have stepD := HomotopyLift.hcomp S
    (HomotopyLift.symm S (RectanglePathLift.transAssoc S
      (PathLift.symm S lF) (PathLift.symm S lE) lG))
    (PathLift.refl S lL)
  have stepE := RectanglePathLift.transAssoc S
    (PathLift.trans S (PathLift.symm S lF) (PathLift.symm S lE)) lG lL
  have stepF := HomotopyLift.hcomp S rev lj3
  have stepG := RectanglePathLift.transAssoc S (PathLift.symm S lD)
    (PathLift.symm S lC) (PathLift.trans S lJ lK)
  have stepH := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S lD))
    (HomotopyLift.symm S (RectanglePathLift.transAssoc S (PathLift.symm S lC) lJ lK))
  exact HomotopyLift.trans S (HomotopyLift.trans S stepA stepB)
    (HomotopyLift.trans S stepC
      (HomotopyLift.trans S stepD
        (HomotopyLift.trans S stepE
          (HomotopyLift.trans S stepF
            (HomotopyLift.trans S stepG stepH)))))
end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
