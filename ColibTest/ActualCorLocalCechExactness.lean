/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.LocalExactness

/-!
# Native local Čech exactness consumers

These consumers use the actual Cor category and graph functor over an arbitrary
field. The first uses only the cover condition and the signed relation. The
second retains arbitrary integer coefficients, including negative coefficients
and zero. The third checks the zero relation without a nonempty-support premise.
The last consumes an actual whole common-support lift after an arbitrary source
morphism, without supplying a pairing comparison or an incidence presentation.

Native in-package consumers of pointed signed local exactness.
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Cor CategoryTheory CategoryTheory.Limits
open Stacks.Chow Function.locallyFinsuppWithin

universe u

variable (k : Type u) [Field k]
  {X Y U V : Scheme.SmoothSite (Spec (.of k))}

example (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (hzero : α ≫ (graphFunctor k).map q = 0) (x : X.left) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
        (graphFunctor k).map g ≫ α =
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
            β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) :=
  exists_nisnevich_cech_boundary k α q hq hzero x

example (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (hzero : α ≫ (graphFunctor k).map q = 0) (x : X.left) (n : ℤ) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
        (graphFunctor k).map g ≫ (n • α) =
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
            β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) := by
  apply exists_nisnevich_cech_boundary k (n • α) q hq _ x
  let Γq : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  change (n • α) ≫ Γq = 0
  change α ≫ Γq = 0 at hzero
  rw [Preadditive.zsmul_comp, hzero, smul_zero]

example (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
        (graphFunctor k).map g ≫ (0 : Cor.mk X ⟶ Cor.mk V) =
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
            β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) :=
  exists_nisnevich_cech_boundary k 0 q hq (by exact zero_comp) x

example (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hzero : α ≫ (graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ a ∈ α.val.support, (integralComponentAt a).subscheme ⟶ C)
    (hr : ∀ a ha, r a ha ≫ j =
      correspondenceGraphPostcompositionMap X.hom V.hom Y.hom q.left
        (MorphismProperty.Over.w q) a)
    (g : U ⟶ X)
    (b : pullback (C := Scheme) (j ≫ pullback.fst X.hom Y.hom) g.left ⟶ V.left)
    (hb : b ≫ q.left = pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫
      j ≫ pullback.snd X.hom Y.hom) :
    ∃ β : Cor.mk U ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      (graphFunctor k).map g ≫ α =
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) :=
  exists_cech_boundary_of_common_support_lift k α q hzero C j r hr g b hb
