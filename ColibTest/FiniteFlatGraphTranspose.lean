/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteFlatTransfer

/-! # Original smooth objects, transposed graphs, and literal transfer degree regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe v u

variable {k : Type u} [Field k] {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)

example : Cor.transposeGraphMap k q ≫ pullback.fst Y.hom X.hom = q.left :=
  Cor.transposeGraphMap_fst k q

example : Cor.transposeGraphMap k q ≫ pullback.snd Y.hom X.hom = 𝟙 X.left :=
  Cor.transposeGraphMap_snd k q

example [IsFinite q.left] [Flat q.left] : Cor.mk Y ⟶ Cor.mk X :=
  Cor.finiteFlatTranspose k q

example [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left] :
    Cor.finiteFlatTranspose k q ≫ (Cor.graphFunctor k).map q =
      (q.left.residueDegree (genericPoint X.left) : ℤ) • 𝟙 (Cor.mk Y) :=
  Cor.finiteFlatTranspose_comp_graph_of_isIntegral k q

example (P : PresheafWithTransfers.{v} k)
    [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left] :
    PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map q) ≫
      PresheafWithTransfers.transfer P (Cor.finiteFlatTranspose k q) =
        (q.left.residueDegree (genericPoint X.left) : ℤ) •
          𝟙 (PresheafWithTransfers.sections P (Cor.mk Y)) :=
  PresheafWithTransfers.transfer_graph_comp_finiteFlatTranspose P q

#print axioms AlgebraicGeometry.Cor.finiteFlatTranspose
#print axioms AlgebraicGeometry.Cor.finiteFlatTranspose_val_apply
#print axioms AlgebraicGeometry.Cor.finiteFlatTranspose_comp_graph_val
#print axioms AlgebraicGeometry.Cor.finiteFlatTranspose_comp_graph_of_isIntegral
#print axioms AlgebraicGeometry.PresheafWithTransfers.transfer_graph_comp_finiteFlatTranspose
