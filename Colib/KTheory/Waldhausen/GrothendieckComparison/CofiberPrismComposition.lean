/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberPrismHomotopy

/-!
# The prescribed cofiber composition prism

Compose the actual triangle-times-interval family with the same explicit standard-triangle
interpolation used by the original cofiber object-loop track. The comparison, nerve and loop
coordinates remain independent, and both nerve faces are the original specified tracks.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/CofiberPrismComposition.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits unitInterval
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The actual three-parameter family, in comparison, nerve and object-loop order. -/
def cofiberPrismCompositionCube : C(unitInterval × (unitInterval × unitInterval), W.Delooping)
    where
  toFun z := realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
    (z.2.1, realizationStdSimplexPathHomotopy
      ((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
        (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide))))
      (realizationEdgePath (simplexEdge.{max u v} 2 0 2 (by decide))) (z.1, z.2.2))
  continuous_toFun := by fun_prop

/-- At nerve time zero the actual identity-cofiber triangle track is retained. -/
theorem cofiberPrismCompositionCube_nerve_zero (r t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, 0, t) =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (r, t) := by
  change realizationSimplicialHomotopy _ (0, _) = _
  rw [ContinuousMap.Homotopy.apply_zero, cofiberObjectLoopTrack_apply,
    realizationEdgeCompositionHomotopy_apply]
  rfl

/-- At nerve time one the original displayed quotient triangle track is retained. -/
theorem cofiberPrismCompositionCube_nerve_one (r t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, 1, t) =
      W.cofiberObjectLoopTrack i q hi hQ (r, t) := by
  change realizationSimplicialHomotopy _ (1, _) = _
  rw [ContinuousMap.Homotopy.apply_one, cofiberObjectLoopTrack_apply,
    realizationEdgeCompositionHomotopy_apply]
  rfl

/-- Each entire edge cylinder is the same original continuous face family. -/
theorem cofiberPrismHomotopy_edge (k : Fin 3) (s t : unitInterval) :
    realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
        (s, SSet.toTop.map (SSet.stdSimplex.δ k) (realizationInterval t)) =
      W.cofiberPrismRealization i q hi hwi hQ
        ((Convexity.StdSimplex.homeomorphI.symm t).map (SimplexCategory.δ k), s) := by
  rw [cofiberPrismRealization_homotopy,
    SimplexCategory.toTopHomeo_symm_naturality_apply]
  rfl

/-- The comparison-one face is the actual original weak-cofibration square. -/
theorem cofiberPrismCompositionCube_comparison_one (s t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (1, s, t) =
      bisimplexRealization W (W.weakObjectSimplex i hwi).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex i hwi).property)
        (Convexity.StdSimplex.homeomorphI.symm t,
          Convexity.StdSimplex.homeomorphI.symm s) := by
  change realizationSimplicialHomotopy _ (s, _) = _
  dsimp only [Prod.fst, Prod.snd]
  rw [ContinuousMap.HomotopyWith.apply_one]
  change realizationSimplicialHomotopy _
    (s, SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
  rw [simplexEdge_02_yoneda, cofiberPrismHomotopy_edge,
    cofiberPrismRealization_middle_face]

/-- The comparison-zero face concatenates the actual source and quotient weak-arrow squares. -/
theorem cofiberPrismCompositionCube_comparison_zero (s t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (0, s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
          ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
            (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
          (Convexity.StdSimplex.homeomorphI.symm
            ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩,
            Convexity.StdSimplex.homeomorphI.symm s)
      else
        bisimplexRealization W (W.weakObjectSimplex (0 : W.zero ⟶ Q)
            (cofiberTwo_quotient_weak W i q hi hwi hQ)).val
          ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
            (W.weakObjectSimplex (0 : W.zero ⟶ Q)
              (cofiberTwo_quotient_weak W i q hi hwi hQ)).property)
          (Convexity.StdSimplex.homeomorphI.symm
            ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩,
            Convexity.StdSimplex.homeomorphI.symm s) := by
  change realizationSimplicialHomotopy _ (s, _) = _
  dsimp only [Prod.fst, Prod.snd]
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change realizationSimplicialHomotopy _
    (s, ((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
      (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide)))) t) = _
  rw [Path.trans_apply]
  split_ifs with h
  · change realizationSimplicialHomotopy _
      (s, SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval _)) = _
    rw [simplexEdge_01_yoneda, cofiberPrismHomotopy_edge,
      cofiberPrismRealization_source_face]
  · change realizationSimplicialHomotopy _
      (s, SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval _)) = _
    rw [simplexEdge_12_yoneda, cofiberPrismHomotopy_edge,
      cofiberPrismRealization_quotient_face]

/-- The original initial vertex stays at the actual chosen basepoint for both moving times. -/
theorem cofiberPrismCompositionCube_loop_zero (r s : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, 0) = W.kBasepoint := by
  change realizationSimplicialHomotopy _ (s, _) = _
  dsimp only [Prod.fst, Prod.snd]
  rw [Path.Homotopy.source]
  exact W.cofiberPrismHomotopy_fixed_vertex i q hi hwi hQ 0 s

/-- The original terminal vertex stays at the actual chosen basepoint for both moving times. -/
theorem cofiberPrismCompositionCube_loop_one (r s : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, 1) = W.kBasepoint := by
  change realizationSimplicialHomotopy _ (s, _) = _
  dsimp only [Prod.fst, Prod.snd]
  rw [Path.Homotopy.target]
  exact W.cofiberPrismHomotopy_fixed_vertex i q hi hwi hQ 2 s

/-- The prescribed cube gives a jointly continuous square of actual based loops. -/
def cofiberPrismCompositionLoops :
    C(unitInterval × unitInterval, Path W.kBasepoint W.kBasepoint) where
  toFun z := {
    toFun t := W.cofiberPrismCompositionCube i q hi hwi hQ (z.1, z.2, t)
    continuous_toFun := by fun_prop
    source' := W.cofiberPrismCompositionCube_loop_zero i q hi hwi hQ z.1 z.2
    target' := W.cofiberPrismCompositionCube_loop_one i q hi hwi hQ z.1 z.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.cofiberPrismCompositionCube i q hi hwi hQ).continuous.comp
      ((continuous_fst.fst).prodMk ((continuous_fst.snd).prodMk continuous_snd))

/-- All three original coordinates survive currying into the actual based-loop space. -/
theorem cofiberPrismCompositionLoops_apply (r s t : unitInterval) :
    W.cofiberPrismCompositionLoops i q hi hwi hQ (r, s) t =
      W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, t) := rfl

end CategoryTheory.Waldhausen.Structure
