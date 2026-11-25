/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.ScalarRectangleLiftOps
public import Colib.Topology.Prespectrum.HomotopySquarePauseRight

/-! Exact scalar terminal pause and three-side collapse for a supplied whole chart boundary. -/
/-! Source: `ScalarChartPause.lean` at Quillen commit
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
variable {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
variable {f₀ g₀ f₁ g₁ : prespectrum V ⟶ prespectrum W}
variable {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁}
variable {l : Path a₀ a₁} {m : Path b₀ b₁}
variable {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
variable {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}

/-- The same terminal constant-half pause as the native `Square.pauseRight` word. -/
def pauseRightParameter (J : p₀.Homotopy ((l.trans p₁).trans m.symm)) :=
  J.trans ((Path.Homotopy.refl (l.trans p₁)).hcomp
    ((Path.Homotopy.transRefl m).symm.symm₂))

/-- The scalar terminal pause and quotient collapse reproduce the entire native paused square. -/
theorem HomotopyLift.pauseRight_square
    {J : p₀.Homotopy ((l.trans p₁).trans m.symm)}
    {N : H₀.RelHomotopy ((L.trans H₁).trans M.symm)}
    (hJ : HomotopyLift S J N)
    (hL : PathLift S l L) (hH₁ : PathLift S p₁ H₁) (hM : PathLift S m M)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (collapsed (pauseRightParameter J) (r, s), x) =
      (N.toSquare.pauseRight).level n (r, (s, x)) := by
  have hBoundary : HomotopyLift S J N.toSquare.toBoundary := by
    intro n r s x
    change prespectrumSimplexFamily S n (J (r, s), x) =
      N.toSquare.level n ((ThreeSideSquare.collapse (r, s)).1,
        ((ThreeSideSquare.collapse (r, s)).2, x))
    rw [Homotopy.RelHomotopy.toSquare_collapse]
    exact hJ n r s x
  have hPause := HomotopyLift.trans S hBoundary
    (HomotopyLift.hcomp S
      (PathLift.refl S (PathLift.trans S hL hH₁))
      (HomotopyLift.symmPath S
        (HomotopyLift.symm S (RectanglePathLift.transRefl S hM))))
  exact HomotopyLift.toSquare S hPause n r s x

end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
