/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrum
public import Colib.KTheory.Waldhausen.Iterated.SimplexStageFaceRealization

/-!
# Barycentric face evaluation throughout the original prespectrum

The entire original simplex face is preserved at every level, including its based loop at zero.

Adapted from Quillen/Waldhausen/SConstruction/Iterated/SimplexTriangleLift.lean:24-51
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} {k l : ℕ}

/-- Barycentric face transport retains the complete original family. -/
theorem prespectrumSimplexFamily_face (S : ModelSimplex V W k)
    (α : ⦋l⦌ ⟶ ⦋k⦌) (n : ℕ) (z : StdSimplex ℝ (Fin (l + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (StdSimplex.map α.toOrderHom z, x) =
      prespectrumSimplexFamily (S.face α) n (z, x) := by
  have hs (r : ℕ) (y : stageSpace r V) :
      stageSimplexBarycentric S r (StdSimplex.map α.toOrderHom z, y) =
        stageSimplexBarycentric (S.face α) r (z, y) := by
    unfold stageSimplexBarycentric
    dsimp only [ContinuousMap.coe_mk]
    have hz : (SimplexCategory.toTopHomeo ⦋k⦌).symm
        (StdSimplex.map α.toOrderHom z) =
        SSet.toTop.map (SSet.stdSimplex.map α)
          ((SimplexCategory.toTopHomeo ⦋l⦌).symm z) := by
      apply (SimplexCategory.toTopHomeo ⦋k⦌).injective
      rw [Homeomorph.apply_symm_apply, SimplexCategory.toTopHomeo_naturality_apply,
        Homeomorph.apply_symm_apply]
      rfl
    rw [hz]
    exact stageSimplexRealization_face r S α y _
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact hs 0 (x t)
  | succ n => exact hs n x

end CategoryTheory.Waldhausen.IteratedS
