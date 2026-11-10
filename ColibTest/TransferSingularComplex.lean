/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Underlying

/-! Actual components, arbitrary signed transfers, differentials and ordinary restriction. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers
open scoped Simplicial

universe u v

noncomputable section

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)

example (n : ℕ) (U : Cor k) :
    ((singularComplex P).X n).obj.obj (op U) = sections P (Cor.simplexProduct U n) :=
  singularComplex_X_obj P n U

example (n : ℕ) {U V : Cor k} (α : U ⟶ V) :
    ((singularComplex P).X n).obj.map (-α).op =
      -transfer P (Cor.simplexExterior n α) := by
  rw [singularComplex_X_map]
  simp

example (n : ℕ) (U : Cor k) :
    ((singularComplex P).d (n + 1) n).hom.app (op U) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U.toSmoothSite)
          ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) :=
  singularComplex_d_app P n U

example : (singularComplex P).d 1 0 = singularFace P 0 0 - singularFace P 0 1 :=
  singularComplex_d_one_zero P

example (Q : PresheafWithTransfers.{v} k) (η : P ⟶ Q) (n : ℕ) (U : Cor k) :
    ((singularComplexMap η).f n).hom.app (op U) =
      η.hom.app (op (Cor.simplexProduct U n)) := singularComplexMap_f_app η n U

example (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    ((singularComplexUnderlyingIso P).hom.f n).app (op U) =
      𝟙 (sections P (Cor.simplexProduct (Cor.mk U) n)) :=
  singularComplexUnderlyingIso_hom_f_app P n U

example : singularComplexFunctor ⋙
      (toPresheaf.{v} k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
    toPresheaf k ⋙ AlgebraicSimplex.singularChainsFunctor k :=
  singularComplexUnderlyingNatIso

example (q r : ℕ) : (singularCochainComplex P q).X ((q : ℤ) - r) ≅
    (singularComplex P).X r := singularCochainXIso P q r

example (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((singularCochainComplex P q).X i) :=
  isZero_singularCochainComplex_X P q i hi

example (q r : ℕ) :
    (singularCochainComplex P q).d ((q : ℤ) - (r + 1)) ((q : ℤ) - r) =
      (singularCochainXIso P q (r + 1)).hom ≫ (singularComplex P).d (r + 1) r ≫
        (singularCochainXIso P q r).inv := singularCochainComplex_d P q r
