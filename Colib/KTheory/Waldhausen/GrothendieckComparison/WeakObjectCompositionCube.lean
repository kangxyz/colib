/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectCompositionRealization
public import Colib.Topology.Realization.TriangleHomotopy

/-! # The specified weak-arrow composition cube

Comparison, nerve/path and object-loop coordinates remain independent.
-/
/-!
## Additional implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionCube.lean`,
lines 28–108,
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

/-- The actual comparison, nerve and object-loop coordinates of the composition triangle. -/
def weakObjectCompositionCube : C(unitInterval × (unitInterval × unitInterval), W.Delooping)
    where
  toFun z := W.weakObjectCompositionRealization f g hf hg
    (StdSimplex.homeomorphI.symm z.2.2,
      SimplexCategory.toTopHomeo ⦋2⦌ (realizationStdSimplexPathHomotopy
        ((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
          (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide))))
        (realizationEdgePath (simplexEdge.{max u v} 2 0 2 (by decide))) (z.1, z.2.1)))
  continuous_toFun := by fun_prop

/-- An original nerve edge retains its exact barycentric realization at every object-loop time. -/
theorem weakObjectCompositionRealization_edge (k : Fin 3) (s t : unitInterval) :
    W.weakObjectCompositionRealization f g hf hg
      (StdSimplex.homeomorphI.symm t,
        SimplexCategory.toTopHomeo ⦋2⦌
          (SSet.toTop.map (SSet.stdSimplex.δ k) (realizationInterval.{max u v} s))) =
      W.weakObjectCompositionRealization f g hf hg
        (StdSimplex.homeomorphI.symm t,
          (StdSimplex.homeomorphI.symm s).map (SimplexCategory.δ k)) := by
  change W.weakObjectCompositionRealization f g hf hg
    (_, SimplexCategory.toTopHomeo ⦋2⦌
      (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ k))
        (realizationInterval.{max u v} s))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  have hs : SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{max u v} s) =
      StdSimplex.homeomorphI.symm s :=
    (SimplexCategory.toTopHomeo ⦋1⦌).apply_symm_apply _
  rw [hs]

/-- The comparison-one face is the whole square of the original composite arrow. -/
theorem weakObjectCompositionCube_one (s t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (1, s, t) =
      bisimplexRealization W
        (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) := by
  change W.weakObjectCompositionRealization f g hf hg (_, SimplexCategory.toTopHomeo ⦋2⦌ _) = _
  dsimp only [_root_.Prod.fst, _root_.Prod.snd]
  rw [ContinuousMap.HomotopyWith.apply_one]
  change W.weakObjectCompositionRealization f g hf hg
    (_, SimplexCategory.toTopHomeo ⦋2⦌
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval s))) = _
  rw [simplexEdge_02_yoneda, weakObjectCompositionRealization_edge,
    weakObjectCompositionRealization_composite]

/-- The comparison-zero face concatenates the two original squares in the nerve coordinate. -/
theorem weakObjectCompositionCube_zero (s t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (0, s, t) =
      if h : (s : ℝ) ≤ 1 / 2 then
        bisimplexRealization W (W.weakObjectSimplex f hf).val
          ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
          (StdSimplex.homeomorphI.symm t,
            StdSimplex.homeomorphI.symm
              ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩)
      else
        bisimplexRealization W (W.weakObjectSimplex g hg).val
          ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex g hg).property)
          (StdSimplex.homeomorphI.symm t,
            StdSimplex.homeomorphI.symm
              ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩) := by
  change W.weakObjectCompositionRealization f g hf hg (_, SimplexCategory.toTopHomeo ⦋2⦌ _) = _
  dsimp only [_root_.Prod.fst, _root_.Prod.snd]
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change W.weakObjectCompositionRealization f g hf hg
    (_, SimplexCategory.toTopHomeo ⦋2⦌
      (((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
        (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide)))) s)) = _
  rw [Path.trans_apply]
  split_ifs with h
  · change W.weakObjectCompositionRealization f g hf hg
      (_, SimplexCategory.toTopHomeo ⦋2⦌
        (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval _))) = _
    rw [simplexEdge_01_yoneda, weakObjectCompositionRealization_edge,
      weakObjectCompositionRealization_first]
  · change W.weakObjectCompositionRealization f g hf hg
      (_, SimplexCategory.toTopHomeo ⦋2⦌
        (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval _))) = _
    rw [simplexEdge_12_yoneda, weakObjectCompositionRealization_edge,
      weakObjectCompositionRealization_second]

end CategoryTheory.Waldhausen.Structure
