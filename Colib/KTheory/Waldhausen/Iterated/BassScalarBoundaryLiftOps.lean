/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.BoundaryOfComparison
public import Colib.Topology.Prespectrum.ActualBoundaryWord
public import Colib.KTheory.Waldhausen.Iterated.ScalarRectangleLiftOps

/-! Whole-level lift of the literal native moving-square boundary word. -/
/-! Source: `BassScalarBoundaryLiftOps.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
  (S : ModelSimplex V W k)
variable {a b c d : StdSimplex ℝ (Fin (k + 1))}
variable {f g h j : prespectrum V ⟶ prespectrum W}
variable {pB : Path a b} {pK : Path b c} {pH : Path a d} {pA : Path d c}
variable {hB : Homotopy f g} {hK : Homotopy g h}
variable {hH : Homotopy f j} {hA : Homotopy j h}

/-- The exact scalar moving-square boundary evaluates to the native boundary at every level. -/
theorem HomotopyLift.boundaryOfComparison
    (lB : PathLift S pB hB) (lH : PathLift S pH hH) (lA : PathLift S pA hA)
    {J : pK.Homotopy ((pB.symm.trans pH).trans pA)}
    {N : hK.RelHomotopy ((hB.symm.trans hH).trans hA)}
    (hJ : HomotopyLift S J N) :
    HomotopyLift S (Path.Homotopy.boundaryOfComparison J)
      (Homotopy.RelHomotopy.actualBoundaryWord N) := by
  unfold Path.Homotopy.boundaryOfComparison
    Homotopy.RelHomotopy.actualBoundaryWord
  have stepR1 := HomotopyLift.hcomp S (PathLift.refl S lB) hJ
  have stepR2 := HomotopyLift.symm S
    (RectanglePathLift.transAssoc S lB (PathLift.trans S (PathLift.symm S lB) lH) lA)
  have stepR3 := HomotopyLift.hcomp S
    (HomotopyLift.symm S
      (RectanglePathLift.transAssoc S lB (PathLift.symm S lB) lH))
    (PathLift.refl S lA)
  have stepR4 := HomotopyLift.hcomp S
    (HomotopyLift.hcomp S
      (HomotopyLift.symm S (PathLift.reflTransSymm S lB))
      (PathLift.refl S lH))
    (PathLift.refl S lA)
  have stepR5 := HomotopyLift.hcomp S
    (RectanglePathLift.reflTrans S lH) (PathLift.refl S lA)
  have route := HomotopyLift.trans S stepR1
    (HomotopyLift.trans S stepR2
      (HomotopyLift.trans S stepR3
        (HomotopyLift.trans S stepR4 stepR5)))
  have step0 := HomotopyLift.symm S (RectanglePathLift.transRefl S lH)
  have step1 := HomotopyLift.hcomp S (PathLift.refl S lH)
    (PathLift.reflTransSymm S lA)
  have step2 := HomotopyLift.symm S
    (RectanglePathLift.transAssoc S lH lA (PathLift.symm S lA))
  have step3 := HomotopyLift.hcomp S (HomotopyLift.symm S route)
    (PathLift.refl S (PathLift.symm S lA))
  exact HomotopyLift.trans S step0
    (HomotopyLift.trans S step1
      (HomotopyLift.trans S step2 step3))
end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
