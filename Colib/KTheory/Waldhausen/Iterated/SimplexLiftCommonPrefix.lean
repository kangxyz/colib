/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftSquareOperations
public import Colib.Topology.Prespectrum.RelativeHomotopyCommonPrefixSquare

/-!
# Exact scalar common-prefix pasting

The scalar surface in any topological space follows the literal native common-prefix cancellation
word, including every association and contraction clock. For a common model simplex, its whole
lift descends through the original three-side collapse to the common-prefix square, at every
level and every point of the independent loop.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters

section Pasting
variable {Z : Type v} [TopologicalSpace Z] {o a b c d e : Z}
  {pC : Path o a} {pD : Path a d} {pF : Path a e}
  {pL : Path o b} {pP : Path b d} {pT : Path o c} {pM : Path c e}

/-- The exact scalar word of native common-prefix cancellation in any topological space. -/
def commonPrefixPasting
    (J : (pC.trans pD).Homotopy (pL.trans pP))
    (K : (pC.trans pF).Homotopy (pT.trans pM)) :
    pT.Homotopy ((pL.trans (pP.trans (pD.symm.trans pF))).trans pM.symm) := by
  have start : pT.Homotopy ((pT.trans pM).trans pM.symm) :=
    (Path.Homotopy.transRefl pT).symm.trans
      (((Path.Homotopy.refl pT).hcomp (Path.Homotopy.reflTransSymm pM)).trans
        (Path.Homotopy.transAssoc pT pM pM.symm).symm)
  have insert : (pC.trans pF).Homotopy ((pC.trans pD).trans (pD.symm.trans pF)) :=
    ((Path.Homotopy.refl pC).hcomp (Path.Homotopy.reflTrans pF).symm).trans
      (((Path.Homotopy.refl pC).hcomp
          ((Path.Homotopy.reflTransSymm pD).hcomp (Path.Homotopy.refl pF))).trans
        (((Path.Homotopy.refl pC).hcomp (Path.Homotopy.transAssoc pD pD.symm pF)).trans
          (Path.Homotopy.transAssoc pC pD (pD.symm.trans pF)).symm))
  exact start.trans ((K.symm.hcomp (Path.Homotopy.refl pM.symm)).trans
    ((insert.hcomp (Path.Homotopy.refl pM.symm)).trans
      (((J.hcomp (Path.Homotopy.refl (pD.symm.trans pF))).hcomp
          (Path.Homotopy.refl pM.symm)).trans
        ((Path.Homotopy.transAssoc pL pP (pD.symm.trans pF)).hcomp
          (Path.Homotopy.refl pM.symm)))))

end Pasting

variable {k : ℕ} {o a b c d e : StdSimplex ℝ (Fin (k + 1))}
  {pC : Path o a} {pD : Path a d} {pF : Path a e}
  {pL : Path o b} {pP : Path b d} {pT : Path o c} {pM : Path c e}

/-- The original three-side descent supplies the four exact scalar boundary tracks. -/
def commonPrefixSquare
    (J : (pC.trans pD).Homotopy (pL.trans pP))
    (K : (pC.trans pF).Homotopy (pT.trans pM)) :
    ParameterSquare pT (pP.trans (pD.symm.trans pF)) pL pM :=
  ParameterSquare.ofBoundary (commonPrefixPasting J K)

variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (S : ModelSimplex V W k)
  {O A B C D E : prespectrum V ⟶ prespectrum W}
  {HC : Homotopy O A} {HD : Homotopy A D} {HF : Homotopy A E}
  {HL : Homotopy O B} {HP : Homotopy B D} {HT : Homotopy O C} {HM : Homotopy C E}
  {J : (pC.trans pD).Homotopy (pL.trans pP)}
  {K : (pC.trans pF).Homotopy (pT.trans pM)}
  {N : (HC.trans HD).RelHomotopy (HL.trans HP)}
  {N' : (HC.trans HF).RelHomotopy (HT.trans HM)}

/-- Every point of the scalar word lifts to the specified original native pasting. -/
theorem HomotopyLift.commonPrefixPasting
    (hC : PathLift S pC HC) (hD : PathLift S pD HD) (hF : PathLift S pF HF)
    (hL : PathLift S pL HL) (hP : PathLift S pP HP) (hT : PathLift S pT HT)
    (hM : PathLift S pM HM) (hJ : HomotopyLift S J N) (hK : HomotopyLift S K N') :
    HomotopyLift S (commonPrefixPasting J K)
      (Homotopy.RelHomotopy.commonPrefixPasting N N') := by
  have hstart := HomotopyLift.trans S (HomotopyLift.symm S (RectanglePathLift.transRefl S hT))
    (HomotopyLift.trans S
      (HomotopyLift.hcomp S (PathLift.refl S hT) (PathLift.reflTransSymm S hM))
      (HomotopyLift.symm S (RectanglePathLift.transAssoc S hT hM (PathLift.symm S hM))))
  have hinsert := HomotopyLift.trans S
    (HomotopyLift.hcomp S (PathLift.refl S hC)
      (HomotopyLift.symm S (RectanglePathLift.reflTrans S hF)))
    (HomotopyLift.trans S
      (HomotopyLift.hcomp S (PathLift.refl S hC)
        (HomotopyLift.hcomp S (PathLift.reflTransSymm S hD) (PathLift.refl S hF)))
      (HomotopyLift.trans S
        (HomotopyLift.hcomp S (PathLift.refl S hC)
          (RectanglePathLift.transAssoc S hD (PathLift.symm S hD) hF))
        (HomotopyLift.symm S
          (RectanglePathLift.transAssoc S hC hD (PathLift.trans S (PathLift.symm S hD) hF)))))
  exact HomotopyLift.trans S hstart
    (HomotopyLift.trans S
      (HomotopyLift.hcomp S (HomotopyLift.symm S hK) (PathLift.refl S (PathLift.symm S hM)))
      (HomotopyLift.trans S
        (HomotopyLift.hcomp S hinsert (PathLift.refl S (PathLift.symm S hM)))
        (HomotopyLift.trans S
          (HomotopyLift.hcomp S
            (HomotopyLift.hcomp S hJ (PathLift.refl S (PathLift.trans S (PathLift.symm S hD) hF)))
            (PathLift.refl S (PathLift.symm S hM)))
          (HomotopyLift.hcomp S
            (RectanglePathLift.transAssoc S hL hP (PathLift.trans S (PathLift.symm S hD) hF))
            (PathLift.refl S (PathLift.symm S hM))))))

/-- The exact whole common-prefix lift survives the original square descent without new clocks. -/
theorem HomotopyLift.commonPrefixSquare
    (hC : PathLift S pC HC) (hD : PathLift S pD HD) (hF : PathLift S pF HF)
    (hL : PathLift S pL HL) (hP : PathLift S pP HP) (hT : PathLift S pT HT)
    (hM : PathLift S pM HM) (hJ : HomotopyLift S J N) (hK : HomotopyLift S K N') :
    SquareLift S (commonPrefixSquare J K)
      (Homotopy.RelHomotopy.commonPrefixSquare N N') :=
  HomotopyLift.toSquare S
    (HomotopyLift.commonPrefixPasting S hC hD hF hL hP hT hM hJ hK)

end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
