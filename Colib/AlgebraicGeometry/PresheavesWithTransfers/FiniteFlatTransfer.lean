/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Transpose
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic

/-!
# The actual finite flat transfer degree on presheaves with transfers

The ordinary pullback along the original graph followed by transfer along the constructed
transposed graph is multiplication by the actual generic residue degree. This uses the
proved native correspondence composition, not a supplied transfer or degree equation.
The opposite composite and radicial invariance are not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)
  [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]

/-- Pullback followed by the actual transposed-graph transfer multiplies sections by the
full generic residue degree, including its inseparable factor. -/
@[colib_tag "COL-1088", colib_ref "MVW2006"
  "Lecture 1, Exercise 1.11, printed p. 6; Lecture 2, Definition 2.1, printed p. 13"
  "adaptation" "the proved native degree identity acts on the original presheaf with transfers"]
theorem transfer_graph_comp_finiteFlatTranspose :
    transfer P ((Cor.graphFunctor k).map q) ≫ transfer P (Cor.finiteFlatTranspose k q) =
      (q.left.residueDegree (genericPoint X.left) : ℤ) • 𝟙 (sections P (Cor.mk Y)) := by
  refine (transfer_comp P (X := Cor.mk Y) (Y := Cor.mk X) (Z := Cor.mk Y)
    (Cor.finiteFlatTranspose k q) ((Cor.graphFunctor k).map q)).symm.trans ?_
  exact (congrArg (fun α : Cor.mk Y ⟶ Cor.mk Y => transfer P α)
    (Cor.finiteFlatTranspose_comp_graph_of_isIntegral k q)).trans (by
      rw [transfer_zsmul, transfer_id])

end AlgebraicGeometry.PresheafWithTransfers
