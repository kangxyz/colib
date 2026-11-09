/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.SignedLocalLift

/-!
# Consumers of actual local Nisnevich graph factorization

These consumers retain the actual distinguished source point and its induced
residue-field isomorphism together with the native Cor factorization. No perfect
field, connectedness, nonzero cycle, reduced support pullback or flat support
hypothesis occurs. The subtraction and zero cases use the same public endpoint.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y V : Scheme.SmoothSite (Spec (.of k))}
  (q : V ⟶ Y) [Etale q.left]
  (hq : ∀ y : Y.left, ∃ v : V.left,
    q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left)

include hq

example (a : pullback (C := Scheme) X.hom Y.hom) (ha : IsFiniteCorrespondencePoint X.hom Y.hom a) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 :=
  exists_nisnevich_graph_factorization_single k a ha q hq x

example (a : pullback (C := Scheme) X.hom Y.hom) (ha : IsFiniteCorrespondencePoint X.hom Y.hom a) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha (-3) :=
  exists_nisnevich_graph_factorization_single_signed k a ha q hq x (-3)

example (α γ : Cor.mk X ⟶ Cor.mk Y) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q = (graphFunctor k).map g ≫ (α - γ) :=
  exists_nisnevich_graph_factorization k (α - γ) q hq x

example :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V, β ≫ (graphFunctor k).map q = 0 := by
  obtain ⟨U, g, hg, u, hu, hr, β, hβ⟩ :=
    exists_nisnevich_graph_factorization k (0 : Cor.mk X ⟶ Cor.mk Y) q hq x
  let γ : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
  let δ : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  change β ≫ δ = γ ≫ (0 : Cor.mk X ⟶ Cor.mk Y) at hβ
  rw [CategoryTheory.Limits.comp_zero] at hβ
  exact ⟨U, g, hg, u, hu, hr, β, hβ⟩

end AlgebraicGeometry.Cor
