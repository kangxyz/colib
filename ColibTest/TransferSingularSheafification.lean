/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Sheafification

/-! Real large-coefficient transfer sheafification, its unit and ordinary comparison. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u

noncomputable section

variable (k : Type u) [Field k]
-- These six checks have no assumed sheafification instances.
example : HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} := inferInstance

example : (Cor.nisnevichTopology k).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) := inferInstance

example : (Cor.nisnevichTopology k).PreservesSheafification
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) := inferInstance

example : HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
    AddCommGrpCat.{u + 1} := inferInstance

example : (SmoothSite.nisnevichTopology (Spec (.of k))).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) := inferInstance

example : (SmoothSite.nisnevichTopology (Spec (.of k))).PreservesSheafification
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) := inferInstance

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]
variable (P : PresheafWithTransfers.{u + 1} k)

example (n : ℕ) : (singularSheafComplex k P).X n =
    (nisnevichSheafify k).obj ((singularComplex P).X n) := singularSheafComplex_X k P n

example (i j : ℕ) : (singularSheafComplex k P).d i j =
    (nisnevichSheafify k).map ((singularComplex P).d i j) :=
  singularSheafComplex_d k P i j

example (n : ℕ) : ((singularSheafUnit k).app P).f n =
    toNisnevichSheafify k ((singularComplex P).X n) := singularSheafUnit_app_f k P n

example :
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (singularSheafComplex k P) ≅
      (AlgebraicSimplex.sheafifiedSingularChainsFunctor k
        (SmoothSite.nisnevichTopology (Spec (.of k)))).obj ((toPresheaf k).obj P) :=
  singularSheafOrdinaryIso k P

example : singularSheafFunctor k ⋙
      (SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
    toPresheaf k ⋙ AlgebraicSimplex.sheafifiedSingularChainsFunctor k
      (SmoothSite.nisnevichTopology (Spec (.of k))) := singularSheafOrdinaryNatIso k

example (q r : ℕ) : (singularSheafCochainComplex k P q).X ((q : ℤ) - r) ≅
    (nisnevichSheafify k).obj ((singularComplex P).X r) :=
  singularSheafCochainXIso k P q r

example (q r : ℕ) :
    (singularSheafCochainComplex k P q).d ((q : ℤ) - (r + 1)) ((q : ℤ) - r) =
      (singularSheafCochainXIso k P q (r + 1)).hom ≫
        (nisnevichSheafify k).map ((singularComplex P).d (r + 1) r) ≫
          (singularSheafCochainXIso k P q r).inv := singularSheafCochainComplex_d k P q r
