/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.KTheory.Waldhausen.Iterated.SimplexStageSpecifications

/-!
# Barycentric evaluation in the original iterated S-prespectrum

The actual simplex family evaluates at every level, including the original based loop space.
The loop and structure parameters remain separate from the barycentric parameter.

Adapted from Quillen/Waldhausen/SConstruction/Iterated/SimplexPrespectrum.lean:28-81 at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} {k : ℕ} (S : ModelSimplex V W k)

/-- The original entire simplex in finite barycentric coordinates. -/
def stageSimplexBarycentric (n : ℕ) :
    C(StdSimplex ℝ (Fin (k + 1)) × stageSpace n V, stageSpace n W) :=
  ⟨fun z ↦ stageSimplexRealization n S
    (z.2, (SimplexCategory.toTopHomeo ⦋k⦌).symm z.1),
    (stageSimplexRealization n S).continuous.comp
      (continuous_snd.prodMk ((SimplexCategory.toTopHomeo ⦋k⦌).symm.continuous.comp
        continuous_fst))⟩

/-- The original loop-space level evaluates the higher family at a separate loop coordinate. -/
def simplexLoopFamily :
    C(StdSimplex ℝ (Fin (k + 1)) × Path (stagePoint 0 V) (stagePoint 0 V),
      Path (stagePoint 0 W) (stagePoint 0 W)) where
  toFun z := {
    toFun t := stageSimplexBarycentric S 0 (z.1, z.2 t)
    continuous_toFun := by fun_prop
    source' := by
      rw [Path.source]
      exact stageSimplexRealization_fixed_point 0 S _
    target' := by
      rw [Path.target]
      exact stageSimplexRealization_fixed_point 0 S _ }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (stageSimplexBarycentric S 0).continuous.comp
      (continuous_fst.fst.prodMk ((Path.continuous_uncurry_iff.mpr continuous_id).comp
        (continuous_fst.snd.prodMk continuous_snd)))

/-- The entire original prespectrum carries the same simplex family, including level zero. -/
def prespectrumSimplexFamily (n : ℕ) :
    C(StdSimplex ℝ (Fin (k + 1)) × (prespectrum V).space n, (prespectrum W).space n) :=
  Nat.casesOn n (simplexLoopFamily S) (stageSimplexBarycentric S)

/-- The higher family fixes the actual original point at every prespectrum level. -/
theorem prespectrumSimplexFamily_point (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) :
    prespectrumSimplexFamily S n (z, (prespectrum V).point n) =
      (prespectrum W).point n := by
  cases n with
  | zero =>
    apply Path.ext
    funext t
    exact stageSimplexRealization_fixed_point 0 S _
  | succ n => exact stageSimplexRealization_fixed_point n S _

/-- No simplex parameter is identified with the independent original structure coordinate. -/
theorem prespectrumSimplexFamily_structure (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum V).space n) (t : unitInterval) :
    prespectrumSimplexFamily S (n + 1) (z, (prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n (prespectrumSimplexFamily S n (z, x)) t := by
  cases n with
  | zero => rfl
  | succ n => exact stageSimplexRealization_structure n S _ t x

/-- Level-zero evaluation keeps the original loop time separate from the whole simplex. -/
theorem prespectrumSimplexFamily_zero_apply (z : StdSimplex ℝ (Fin (k + 1)))
    (x : Path (stagePoint 0 V) (stagePoint 0 V)) (t : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      prespectrumSimplexFamily S 0 (z, x)) t = stageSimplexBarycentric S 0 (z, x t) := rfl

end CategoryTheory.Waldhausen.IteratedS
