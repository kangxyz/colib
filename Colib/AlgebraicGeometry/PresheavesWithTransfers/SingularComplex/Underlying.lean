/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains

/-!
# Ordinary restriction of the genuine transfer singular complex

Both existing singular constructions use the same literal relative products.
Graph compatibility therefore identifies their terms by identity maps, and the
ordered alternating-face formulas identify every differential. This gives a
natural isomorphism of actual chain complexes, not merely a termwise comparison.

This adapts the ordinary-comparison part of
`Motivic/Transfers/SingularComplex/Presheaf.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`. The original source used a categorical
product model for its ordinary complex. Colib already uses literal products, so
its extra categorical-product transport is unnecessary; all original face signs,
restriction maps and coefficient morphisms are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Graph restriction of a transfer singular term is the existing ordinary term. -/
def singularTermUnderlyingIso (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (toPresheaf k).obj ((singularComplex P).X n) ≅
      ((AlgebraicSimplex.singularChainsFunctor k).obj ((toPresheaf k).obj P)).X n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    change transfer P (Cor.simplexExterior n ((Cor.graphFunctor k).map f.unop)) ≫ 𝟙 _ =
      𝟙 _ ≫ transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productMap f.unop (𝟙 (AlgebraicSimplex.smoothSiteObj k n))))
    simpa only [Category.comp_id, Category.id_comp] using!
      congrArg (transfer P) (Cor.simplexExterior_graph n f.unop))

/-- The termwise comparison is the identity on the actual original product sections. -/
@[simp]
theorem singularTermUnderlyingIso_hom_app (P : PresheafWithTransfers.{v} k)
    (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    (singularTermUnderlyingIso P n).hom.app (op U) =
      𝟙 (sections P (Cor.simplexProduct (Cor.mk U) n)) := rfl

/-- The actual differentials agree after forgetting transfers. -/
theorem singularComplexUnderlying_d_app (P : PresheafWithTransfers.{v} k)
    (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    ((toPresheaf k).map ((singularComplex P).d (n + 1) n)).app (op U) =
      (((AlgebraicSimplex.singularChainsFunctor k).obj ((toPresheaf k).obj P)).d
        (n + 1) n).app (op U) := by
  rw [AlgebraicSimplex.singularChainsFunctor_obj_d_app]
  exact singularComplex_d_app P n (Cor.mk U)

/-- Forgetting genuine transfers recovers the actual ordinary chain complex. -/
def singularComplexUnderlyingIso (P : PresheafWithTransfers.{v} k) :
    ((toPresheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj (singularComplex P) ≅
      (AlgebraicSimplex.singularChainsFunctor k).obj ((toPresheaf k).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (singularTermUnderlyingIso P) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst i
    apply NatTrans.ext
    funext U
    change (𝟙 _) ≫
      (((AlgebraicSimplex.singularChainsFunctor k).obj ((toPresheaf k).obj P)).d
        (j + 1) j).app U =
      ((toPresheaf k).map ((singularComplex P).d (j + 1) j)).app U ≫ (𝟙 _)
    simpa only [Category.id_comp, Category.comp_id] using!
      (singularComplexUnderlying_d_app P j U.unop).symm)

/-- The all-degree comparison retains the literal identity on sections. -/
@[simp]
theorem singularComplexUnderlyingIso_hom_f_app (P : PresheafWithTransfers.{v} k)
    (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    ((singularComplexUnderlyingIso P).hom.f n).app (op U) =
      𝟙 (sections P (Cor.simplexProduct (Cor.mk U) n)) := rfl

/-- The actual comparison is natural in the transfer presheaf and its coefficients. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/SingularComplex/Presheaf.lean: singularComplexUnderlyingNatIso"
  "adaptation" "Literal-product ordinary restriction comparison"]
def singularComplexUnderlyingNatIso :
    singularComplexFunctor ⋙ (toPresheaf.{v} k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      toPresheaf k ⋙ AlgebraicSimplex.singularChainsFunctor k :=
  NatIso.ofComponents singularComplexUnderlyingIso (by
    intro P Q η
    ext n : 1
    apply NatTrans.ext
    funext U
    change η.hom.app (op (Cor.simplexProduct (Cor.mk U.unop) n)) ≫ 𝟙 _ =
      𝟙 _ ≫ η.hom.app (op (Cor.simplexProduct (Cor.mk U.unop) n))
    simp only [Category.comp_id, Category.id_comp])

end AlgebraicGeometry.PresheafWithTransfers
