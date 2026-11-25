/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ProjectionPasteLift
public import Colib.Topology.Prespectrum.RelativeHomotopyStrictSquarePasting

/-!
# The exact scalar strict-source evaluation pasting word

The original constant-source specialization inserts two reversed reflexive paths before its
projection-square cancellation. These insertions and all their original time subdivisions are
retained explicitly, so the resulting native lift is equality of the complete chosen surface.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity
open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputStrictPaste

/-- The actual inverse-reflexive insertion preceding strict-source cancellation. -/
def insert {T : Type*} [TopologicalSpace T] {a b : T} (p : Path a b) :
    p.Homotopy ((Path.refl a).symm.trans p) :=
  (Path.Homotopy.reflTrans p).symm.cast rfl (by rfl)

/-- The scalar source remains the original constant path for every time. -/
theorem constant_source {T : Type*} [TopologicalSpace T] (a : T) :
    (Path.refl a).symm.trans (Path.refl a) = Path.refl a := by
  apply Path.ext
  funext s
  rw [Path.trans_apply]
  split <;> rfl

/-- The complete original strict-source pasting, including both reflexive insertion stages. -/
def parameter {T : Type*} [TopologicalSpace T] {o c d e f m : T}
    {pT : Path o m} {pLp : Path o c} {pPp : Path c d} {pKp : Path m d}
    {pLm : Path o e} {pPm : Path e f} {pKm : Path m f}
    (Jp : (pLp.trans pPp).Homotopy (pT.trans pKp))
    (Jm : (pLm.trans pPm).Homotopy (pT.trans pKm)) :
    (Path.refl o).Homotopy
      ((pLp.trans (pPp.trans ((pKp.symm.trans pKm).trans pPm.symm))).trans pLm.symm) :=
  (Path.Homotopy.pasteProjectionSquares (Jp.trans (insert (pT.trans pKp)))
    (Jm.trans (insert (pT.trans pKm)))).cast (constant_source o) rfl

/-- The exact native reversed-reflexive insertion used by strict-source pasting. -/
def nativeInsert {E F : Topology.LoopPrespectrum.{u}} {a b : E ⟶ F} (H : Homotopy a b) :
    H.RelHomotopy ((Topology.LoopPrespectrum.Homotopy.refl a).symm.trans H) :=
  ((Homotopy.RelHomotopy.reflTrans H).symm).ofLevels H
    ((Topology.LoopPrespectrum.Homotopy.refl a).symm.trans H) (fun _ => rfl)
    (fun n => Homotopy.trans_level_congr _ _ _ _ n rfl rfl)

/-- Original insertion is retained pointwise at both native parameters. -/
theorem insert_native
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p : Path a b}
    {f g : prespectrum V ⟶ prespectrum W} {H : Homotopy f g}
    (hp : PathLift S p H) : HomotopyLift S (insert p) (nativeInsert H) :=
  HomotopyLift.symm S (RectanglePathLift.reflTrans S hp)

/-- Native constant-source cancellation keeps the exact whole scalar word and all its seams. -/
theorem native
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k)
    {o c d e f m : StdSimplex ℝ (Fin (k + 1))}
    {O C D E F M : prespectrum V ⟶ prespectrum W}
    {pT : Path o m} {pLp : Path o c} {pPp : Path c d} {pKp : Path m d}
    {pLm : Path o e} {pPm : Path e f} {pKm : Path m f}
    {hT : Homotopy O M} {hLp : Homotopy O C} {hPp : Homotopy C D}
    {hKp : Homotopy M D} {hLm : Homotopy O E} {hPm : Homotopy E F}
    {hKm : Homotopy M F}
    (lT : PathLift S pT hT) (lLp : PathLift S pLp hLp) (lPp : PathLift S pPp hPp)
    (lKp : PathLift S pKp hKp) (lLm : PathLift S pLm hLm)
    (lPm : PathLift S pPm hPm) (lKm : PathLift S pKm hKm)
    {Jp : (pLp.trans pPp).Homotopy (pT.trans pKp)}
    {Jm : (pLm.trans pPm).Homotopy (pT.trans pKm)}
    {Np : (hLp.trans hPp).RelHomotopy (hT.trans hKp)}
    {Nm : (hLm.trans hPm).RelHomotopy (hT.trans hKm)}
    (lp : HomotopyLift S Jp Np) (lm : HomotopyLift S Jm Nm) :
    HomotopyLift S (parameter Jp Jm)
      (Homotopy.RelHomotopy.pasteStrictSourceSquares Np Nm) := by
  have l0 : PathLift S (Path.refl o) (Topology.LoopPrespectrum.Homotopy.refl O) := by
    intro n t x
    have h := lT n 0 x
    rw [pT.source, hT.at_zero] at h
    exact h
  have h := HomotopyLift.pasteProjectionSquares S l0 l0 lT lLp lPp lKp lLm lPm lKm
    (HomotopyLift.trans S lp (insert_native S (PathLift.trans S lT lKp)))
    (HomotopyLift.trans S lm (insert_native S (PathLift.trans S lT lKm)))
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputStrictPaste
