/-
Copyright (c) 2026 Colib contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Topology

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

noncomputable section

variable (k : Type u) [Field k]

example (X : SmoothSite (Spec (.of k))) : Cor.IsNisnevichCover k (𝟙 X) :=
  Cor.isNisnevichCover_id k X

example {X Y V : SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk Y) (q : V ⟶ Y) (hq : Cor.IsNisnevichCover k q) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Cor.IsNisnevichCover k g ∧
      ∃ β : Cor.mk U ⟶ Cor.mk V,
        β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ α :=
  Cor.exists_nisnevich_cover_graph_factorization k α q hq

example (X : Cor k) (R : Sieve X) (hR : R ∈ Cor.nisnevichTopology k X) :
    ∃ (Y : Cor k) (q : Y ⟶ X), R q ∧
      Sieve.generate (Presieve.singleton q) ∈ Cor.nisnevichTopology k X :=
  Cor.principal_covering_basis k X R hR

example {X : SmoothSite (Spec (.of k))} {R : Sieve (Cor.mk X)}
    (hR : R ∈ Cor.nisnevichTopology k (Cor.mk X)) :
    R.functorPullback (Cor.graphFunctor k) ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) X :=
  Cor.graph_functorPullback_mem_nisnevichTopology k hR
