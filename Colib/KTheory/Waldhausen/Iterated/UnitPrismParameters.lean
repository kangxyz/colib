/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.UnitPrismNodes
public import Colib.KTheory.Waldhausen.Iterated.ScalarRouteExtraction

/-! The original five-piece unit-track recipe inside the six full reference nodes. Its initial
associator and both original primitive triangle pastings retain their exact time subdivisions. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.UnitPrismParameters

open SmallWaldhausenCategory

/-- The original geometric diamond uses its reversed first triangle then its second triangle. -/
def geometric :
    ((edge 0 1 : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 6)) _).trans (edge 1 4)).Homotopy
      ((edge 0 3).trans (edge 3 4)) :=
  (triangle UnitPrismNodes.geometricFirst).symm.trans
    (triangle UnitPrismNodes.geometricSecond)

/-- The original normalization diamond retains its two individually ordered triangles. -/
def normalization :
    ((edge 1 4 : Path (StdSimplex.single 1 : StdSimplex ℝ (Fin 6)) _).trans (edge 4 5)).Homotopy
      ((edge 1 2).trans (edge 2 5)) :=
  (triangle UnitPrismNodes.normalizationFirst).symm.trans
    (triangle UnitPrismNodes.normalizationSecond)

/-- The unchanged five-piece recipe starts with the actual left-associated source path. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/UnitPrismParameters.lean:23-47"
  "adaptation" "Original five-piece scalar unit prism with its original time cuts"]
def parameter :
    (((edge 0 1 : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 6)) _).trans (edge 1 2)).trans
      (edge 2 5)).Homotopy ((edge 0 3).trans ((edge 3 4).trans (edge 4 5))) :=
  (Path.Homotopy.transAssoc (edge 0 1) (edge 1 2) (edge 2 5)).trans
    (((Path.Homotopy.refl (edge 0 1)).hcomp normalization.symm).trans
      ((Path.Homotopy.transAssoc (edge 0 1) (edge 1 4) (edge 4 5)).symm.trans
        ((geometric.hcomp (Path.Homotopy.refl (edge 4 5))).trans
          (Path.Homotopy.transAssoc (edge 0 3) (edge 3 4) (edge 4 5)))))

/-- Whole lifts of the two actual primitive pastings lift the same five native operations.
The two copies of G and N are extracted from their actual distinct reference edges. -/
theorem parameter_lift {V W : WideSubcategory preservesZero.{u}} (S : ModelSimplex V W 5)
    {a b c : prespectrum V ⟶ prespectrum W}
    (G : Homotopy a b) (N : Homotopy b c) (A : Homotopy a a)
    (B : Homotopy b b) (D : Homotopy c c)
    (JG : (G.trans B).RelHomotopy (A.trans G))
    (JN : (B.trans N).RelHomotopy (N.trans D))
    (hG : HomotopyLift S geometric JG) (hN : HomotopyLift S normalization JN) :
    HomotopyLift S parameter
      ((Homotopy.RelHomotopy.transAssoc G N D).trans
        (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
          ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
            ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
              (Homotopy.RelHomotopy.transAssoc A G N))))) := by
  have g01 := PathLift.trans_left S (HomotopyLift.source S hG)
  have b14 := PathLift.trans_right S (HomotopyLift.source S hG)
  have a03 := PathLift.trans_left S (HomotopyLift.target S hG)
  have g34 := PathLift.trans_right S (HomotopyLift.target S hG)
  have n45 := PathLift.trans_right S (HomotopyLift.source S hN)
  have n12 := PathLift.trans_left S (HomotopyLift.target S hN)
  have d25 := PathLift.trans_right S (HomotopyLift.target S hN)
  exact HomotopyLift.trans S (RectanglePathLift.transAssoc S g01 n12 d25)
    (HomotopyLift.trans S
      (HomotopyLift.hcomp S (PathLift.refl S g01) (HomotopyLift.symm S hN))
      (HomotopyLift.trans S (HomotopyLift.symm S (RectanglePathLift.transAssoc S g01 b14 n45))
        (HomotopyLift.trans S (HomotopyLift.hcomp S hG (PathLift.refl S n45))
          (RectanglePathLift.transAssoc S a03 g34 n45))))

end CategoryTheory.Waldhausen.IteratedS.UnitPrismParameters
