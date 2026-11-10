/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.SignedShift

/-! Actual signed shift components of transfer complexes and sheafified transfer complexes. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.PresheafWithTransfers

universe u v

noncomputable section

variable {k : Type u} [Field k]

example (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    singularCochainComplex P q ≅ (singularCochainComplex P 0)⟦-(q : ℤ)⟧ :=
  singularCochainShiftIso P q

example (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainShiftIso P q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularCochainXIso P q r).hom ≫ (singularShiftedCochainXIso P q r).inv) :=
  singularCochainShiftIso_hom_f P q r

example (P : PresheafWithTransfers.{v} k) (r : ℕ) :
    (singularCochainShiftIso P 2).hom.f ((2 : ℤ) - r) =
      (singularCochainXIso P 2 r).hom ≫ (singularShiftedCochainXIso P 2 r).inv :=
  singularCochainShiftIso_two_hom_f P r

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

example (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    (singularSheafCochainShiftIso k P q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularSheafCochainXIso k P q r).hom ≫
          (singularSheafShiftedCochainXIso k P q r).inv) :=
  singularSheafCochainShiftIso_hom_f k P q r

example (P : PresheafWithTransfers.{u + 1} k) (q r s : ℕ) :
    ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧).d ((q : ℤ) - r) ((q : ℤ) - s) =
      (-1 : ℤ) ^ q •
        ((singularSheafShiftedCochainXIso k P q r).hom ≫
          (nisnevichSheafify k).map ((singularComplex P).d r s) ≫
            (singularSheafShiftedCochainXIso k P q s).inv) :=
  singularSheafShiftedCochain_d k P q r s
