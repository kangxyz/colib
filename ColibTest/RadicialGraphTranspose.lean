/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialTransfer

/-! # Radicial graph cancellation and actual two-sided transfer-degree regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow

universe v u

example {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f] (a : A) :
    0 < f.residueDegree a :=
  f.residueDegree_pos_of_isFinite a

example {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f]
    (hf : Function.Injective f) (c : AlgebraicCycle A ℤ) (a : A) :
    finiteCyclePushforward f c (f a) = c a * (f.residueDegree a : ℤ) :=
  finiteCyclePushforward_apply_of_injective f hf c a

variable {k : Type u} [Field k] {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)

example [IsFinite q.left] [UniversallyInjective q.left]
    (T : Scheme.SmoothSite (Spec (.of k))) :
    Function.Injective (finiteCyclePushforward (Cor.graphTargetMap k T q)) :=
  finiteCyclePushforward_injective_of_injective _ (Cor.graphTargetMap k T q).injective

example [IsFinite q.left] [UniversallyInjective q.left] (T : Cor k)
    (α β : T ⟶ Cor.mk X)
    (h : α ≫ (Cor.graphFunctor k).map q = β ≫ (Cor.graphFunctor k).map q) : α = β :=
  (cancel_mono ((Cor.graphFunctor k).map q)).mp h

example [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]
    [UniversallyInjective q.left] :
    incidenceTorPairing X.hom Y.hom X.hom
        (graphCorrespondenceOfComponents X.hom Y.hom q.left (MorphismProperty.Over.w q)
          (Cor.finite_genericPoints k (Cor.mk X)))
        (Cor.finiteFlatTranspose k q) =
      (q.left.residueDegree (genericPoint X.left) : ℤ) •
        graphCorrespondenceOfComponents X.hom X.hom (𝟙 X.left) (Category.id_comp _)
          (Cor.finite_genericPoints k (Cor.mk X)) :=
  Cor.graph_comp_finiteFlatTranspose_of_universallyInjective k q

example (P : PresheafWithTransfers.{v} k)
    [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]
    [UniversallyInjective q.left] :
    PresheafWithTransfers.transfer P (Cor.finiteFlatTranspose k q) ≫
      PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map q) =
        (q.left.residueDegree (genericPoint X.left) : ℤ) •
          𝟙 (PresheafWithTransfers.sections P (Cor.mk X)) :=
  PresheafWithTransfers.transfer_finiteFlatTranspose_comp_graph P q

example (P : PresheafWithTransfers.{v} k)
    [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left] :
    PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map q) ≫
      PresheafWithTransfers.transfer P (Cor.finiteFlatTranspose k q) =
        (q.left.residueDegree (genericPoint X.left) : ℤ) •
          𝟙 (PresheafWithTransfers.sections P (Cor.mk Y)) :=
  PresheafWithTransfers.transfer_graph_comp_finiteFlatTranspose P q

#print axioms AlgebraicGeometry.Scheme.Hom.residueDegree_pos_of_isFinite
#print axioms Stacks.Chow.finiteCyclePushforward_injective_of_injective
#print axioms AlgebraicGeometry.Cor.graph_map_mono_of_finite_universallyInjective
#print axioms AlgebraicGeometry.Cor.graph_comp_finiteFlatTranspose_of_universallyInjective
#print axioms AlgebraicGeometry.PresheafWithTransfers.transfer_finiteFlatTranspose_comp_graph
