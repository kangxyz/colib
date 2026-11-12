/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RadicialTranspose
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteFlatTransfer

/-!
# Both actual radicial transfer composites

For a finite flat radicial morphism between integral original smooth-site objects, transfer
along its constructed transposed graph followed by ordinary graph pullback is multiplication
by the full generic residue degree. Together with the reverse order this gives both actual
transfer equations. No purely inseparable field-base-change equivalence is assumed or claimed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)
  [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]
  [UniversallyInjective q.left]

/-- The actual radicial transposed-graph transfer followed by graph pullback is multiplication
by the original full generic residue degree on the original source section group. -/
@[colib_tag "COL-1091", colib_ref "MVW2006"
  "Lecture 1, Exercise 1.11, printed p. 6; Lecture 2, Definition 2.1, printed p. 13"
  "adaptation" "the proved opposite radicial correspondence identity on the original PST"]
theorem transfer_finiteFlatTranspose_comp_graph :
    transfer P (Cor.finiteFlatTranspose k q) ≫ transfer P ((Cor.graphFunctor k).map q) =
      (q.left.residueDegree (genericPoint X.left) : ℤ) • 𝟙 (sections P (Cor.mk X)) := by
  refine (transfer_comp P (X := Cor.mk X) (Y := Cor.mk Y) (Z := Cor.mk X)
    ((Cor.graphFunctor k).map q) (Cor.finiteFlatTranspose k q)).symm.trans ?_
  exact (congrArg (fun α : Cor.mk X ⟶ Cor.mk X => transfer P α)
    (Cor.graph_comp_finiteFlatTranspose_of_universallyInjective k q)).trans (by
      rw [transfer_zsmul, transfer_id])

end AlgebraicGeometry.PresheafWithTransfers
