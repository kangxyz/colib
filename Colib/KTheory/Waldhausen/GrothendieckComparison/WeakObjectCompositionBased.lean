/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectCompositionCube

/-! # Chosen-zero faces of the weak-arrow composition cube

Comparison, nerve/path and object-loop coordinates remain independent.
-/
/-!
## Additional implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionBased.lean`,
lines 77–105,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original declarations, full coordinates, hypotheses and universes are retained.
Only native namespaces, precise imports and line wrapping change. Source-only, UNCOMPILED.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity unitInterval
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- Comparison and nerve time preserve the actual initial loop endpoint. -/
theorem weakObjectCompositionCube_loop_zero (r s : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, s, 0) = W.kBasepoint := by
  change W.weakObjectCompositionRealization f g hf hg (StdSimplex.homeomorphI.symm 0, _) = _
  rw [StdSimplex.homeomorphI_symm_zero, weakObjectCompositionRealization_vertex]

/-- Comparison and nerve time preserve the actual terminal loop endpoint. -/
theorem weakObjectCompositionCube_loop_one (r s : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, s, 1) = W.kBasepoint := by
  change W.weakObjectCompositionRealization f g hf hg (StdSimplex.homeomorphI.symm 1, _) = _
  rw [StdSimplex.homeomorphI_symm_one, weakObjectCompositionRealization_vertex]

/-- The specified cube is a jointly continuous square in the original based-loop space. -/
def weakObjectCompositionLoops :
    C(unitInterval × unitInterval, Path W.kBasepoint W.kBasepoint) where
  toFun z := {
    toFun t := W.weakObjectCompositionCube f g hf hg (z.1, z.2, t)
    continuous_toFun := by fun_prop
    source' := W.weakObjectCompositionCube_loop_zero f g hf hg z.1 z.2
    target' := W.weakObjectCompositionCube_loop_one f g hf hg z.1 z.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.weakObjectCompositionCube f g hf hg).continuous.comp
      ((continuous_fst.fst).prodMk ((continuous_fst.snd).prodMk continuous_snd))

/-- Every comparison, nerve and object-loop coordinate remains the originally specified one. -/
theorem weakObjectCompositionLoops_apply (r s t : unitInterval) :
    W.weakObjectCompositionLoops f g hf hg (r, s) t =
      W.weakObjectCompositionCube f g hf hg (r, s, t) := rfl

end CategoryTheory.Waldhausen.Structure
