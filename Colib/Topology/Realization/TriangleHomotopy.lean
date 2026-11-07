/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Triangle
public import Colib.Analysis.Convex.StdSimplex.PathHomotopy

/-!
# Specified affine homotopies for realized triangles

The homotopy is data, not a choice from the existence of a homotopy. Paths are pulled
into the finite simplex, interpolated with the native affine weights, and mapped back
through the specified characteristic map. All endpoint casts remain explicit.

Implementation provenance: only `realizationStdSimplexPathHomotopy`,
`realizationEdgeCompositionHomotopy` and `realizationEdgeCompositionHomotopy_apply`
from `Quillen/Topology/ClassifyingSpace/ArrowPaths.lean`, lines 146–212, at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The earlier declarations already have native owners.
The affine primitive is the existing `Convexity.StdSimplex.pathHomotopy`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval

namespace SSet

/-- All paths with the same endpoints in a realized finite simplex are homotopic. -/
def realizationStdSimplexPathHomotopy {n : ℕ}
    {x y : |(Δ[n] : SSet.{u})|} (p q : Path x y) : p.Homotopy q := by
  let e := SimplexCategory.toTopHomeo (SimplexCategory.mk n)
  have H := (Convexity.StdSimplex.pathHomotopy (p.map e.continuous)
    (q.map e.continuous)).map ⟨e.symm, e.symm.continuous⟩
  have H' := H.pathCast (e.symm_apply_apply x).symm (e.symm_apply_apply y).symm
  refine H'.cast ?_ ?_ <;> ext t <;> exact e.symm_apply_apply _

/-- A simplicial triangle gives the actual relative path homotopy expressing
composition of its two short edges as its long edge. -/
def realizationEdgeCompositionHomotopy
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)).Homotopy
      (realizationEdgePath e₀₂) := by
  let p := realizationEdgePath (simplexEdge.{u} 2 0 1 (by decide))
  let q := realizationEdgePath (simplexEdge.{u} 2 1 2 (by decide))
  let r := realizationEdgePath (simplexEdge.{u} 2 0 2 (by decide))
  let f := (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom
  have hp (t) : f (p t) = realizationEdgePath e₀₁ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    have hface := simplexEdge_01_yoneda
    rw [hface]
    exact realizationEdgePath_triangle_face e₀₁ s.simplex 2 s.d₂ t
  have hq (t) : f (q t) = realizationEdgePath e₁₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    have hface := simplexEdge_12_yoneda
    rw [hface]
    exact realizationEdgePath_triangle_face e₁₂ s.simplex 0 s.d₀ t
  have hr (t) : f (r t) = realizationEdgePath e₀₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    have hface := simplexEdge_02_yoneda
    rw [hface]
    exact realizationEdgePath_triangle_face e₀₂ s.simplex 1 s.d₁ t
  have h₀ : realizationPoint x₀ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 0)) := by
    simpa using (hp 0).symm
  have h₂ : realizationPoint x₂ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 2)) := by
    simpa using (hq 1).symm
  have H := ((realizationStdSimplexPathHomotopy (p.trans q) r).map f).pathCast h₀ h₂
  refine H.cast ?_ ?_
  · ext t
    change ((p.trans q).map f.continuous) t =
      ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)) t
    rw [Path.map_trans]
    simp only [Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  · ext t
    exact hr t

/-- The explicit composition track retains the full standard-triangle interpolation. -/
theorem realizationEdgeCompositionHomotopy_apply
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) (a t : unitInterval) :
    realizationEdgeCompositionHomotopy s (a, t) =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
        (realizationStdSimplexPathHomotopy
          ((realizationEdgePath (simplexEdge.{u} 2 0 1 (by decide))).trans
            (realizationEdgePath (simplexEdge.{u} 2 1 2 (by decide))))
          (realizationEdgePath (simplexEdge.{u} 2 0 2 (by decide))) (a, t)) := rfl

end SSet
