/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Complex

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.PresheafWithTransfers
universe w u
variable (k : Type u) [Field k]
-- These actual-object checks precede all optional sheafification hypotheses.
example (q : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicComplex k q

example (q r : ℕ) :
    (SheafWithTransfers.toSheaf k).obj
        ((motivicComplex k q).X ((q : ℤ) - r)) ≅
      ((AlgebraicSimplex.sheafifiedSingularChainsFunctor k
        (SmoothSite.nisnevichTopology (Spec (.of k)))).obj
          ((toPresheaf k).obj (reducedTorus k q))).X r :=
  motivicComplexOrdinaryXIso k q r

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

example (q : ℕ) : motivicComplex k q =
    (singularSheafCochainComplex k (reducedTorus k q) 0)⟦-(q : ℤ)⟧ :=
  motivicComplex_eq k q

example (q r : ℕ) :
    (motivicComplexPlacementIso k q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularSheafCochainXIso k (reducedTorus k q) q r).hom ≫
          (motivicComplexXIso k q r).inv) :=
  motivicComplexPlacementIso_hom_f k q r

example : motivicComplex k 0 ≅
    singularSheafCochainComplex k
      ((representableLarge k).obj (Cor.mk (SmoothSite.base (Spec (.of k))))) 0 :=
  motivicComplexZeroInputIso k

example : (motivicComplex k 1).X 0 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 1)).X 1) :=
  motivicComplexOneXZeroIso k

example : (motivicComplex k 1).d 0 1 =
    -((motivicComplexOneXZeroIso k).hom ≫
      ((nisnevichSheafify k).map (singularFace (reducedTorus k 1) 0 (0 : Fin 2)) -
        (nisnevichSheafify k).map (singularFace (reducedTorus k 1) 0 (1 : Fin 2))) ≫
      (motivicComplexOneXOneIso k).inv) :=
  motivicComplex_one_d_zero_one k

example : (motivicComplex k 2).d 1 2 =
    (motivicComplexTwoXOneIso k).hom ≫
      ((nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (0 : Fin 2)) -
        (nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (1 : Fin 2))) ≫
      (motivicComplexTwoXTwoIso k).inv :=
  motivicComplex_two_d_one_two k
