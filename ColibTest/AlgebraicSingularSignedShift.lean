/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Simplex.SignedShift

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v w

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) :
    (AlgebraicSimplex.singularCochainsFunctor R q).obj P ≅
      ((AlgebraicSimplex.singularCochainsFunctor R 0).obj P)⟦-(q : ℤ)⟧ :=
  AlgebraicSimplex.singularCochainsShiftIso R P q

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (AlgebraicSimplex.singularCochainsShiftIso R P q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((AlgebraicSimplex.singularCochainsXIso R P q r).hom ≫
          (AlgebraicSimplex.singularCochainsShiftedXIso R P q r).inv) :=
  AlgebraicSimplex.singularCochainsShiftIso_hom_f R P q r

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) :
    (AlgebraicSimplex.singularCochainsShiftIso R P 1).hom.f 0 =
      -((AlgebraicSimplex.singularCochainsXIso R P 1 1).hom ≫
        (AlgebraicSimplex.singularCochainsShiftedXIso R P 1 1).inv) := by
  simpa using AlgebraicSimplex.singularCochainsShiftIso_hom_f R P 1 1

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (r : ℕ) :
    (AlgebraicSimplex.singularCochainsShiftIso R P 2).hom.f ((2 : ℤ) - r) =
      (AlgebraicSimplex.singularCochainsXIso R P 2 r).hom ≫
        (AlgebraicSimplex.singularCochainsShiftedXIso R P 2 r).inv :=
  AlgebraicSimplex.singularCochainsShiftIso_two_hom_f R P r

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) (i j : ℤ) :
    (AlgebraicSimplex.singularCochainsShiftIso R P q).hom.f i ≫
        (((AlgebraicSimplex.singularCochainsFunctor R 0).obj P)⟦-(q : ℤ)⟧).d i j =
      ((AlgebraicSimplex.singularCochainsFunctor R q).obj P).d i j ≫
        (AlgebraicSimplex.singularCochainsShiftIso R P q).hom.f j :=
  AlgebraicSimplex.singularCochainsShiftIso_comm R P q i j

example {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (q : ℕ) :
    (AlgebraicSimplex.singularCochainsFunctor R q).map α ≫
        (AlgebraicSimplex.singularCochainsShiftIso R Q q).hom =
      (AlgebraicSimplex.singularCochainsShiftIso R P q).hom ≫
        (CategoryTheory.shiftFunctor
          (CochainComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ℤ) (-(q : ℤ))).map
          ((AlgebraicSimplex.singularCochainsFunctor R 0).map α) :=
  AlgebraicSimplex.singularCochainsShiftIso_naturality R α q

variable (J : GrothendieckTopology (SmoothSite (Spec (.of R)))) [HasSheafify J A]

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) :
    (AlgebraicSimplex.sheafifiedSingularCochainsFunctor R J q).obj P ≅
      ((AlgebraicSimplex.sheafifiedSingularCochainsFunctor R J 0).obj P)⟦-(q : ℤ)⟧ :=
  AlgebraicSimplex.sheafifiedSingularCochainsShiftIso R J P q

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (AlgebraicSimplex.sheafifiedSingularCochainsShiftIso R J P q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((AlgebraicSimplex.sheafifiedSingularCochainsXIso R J P q r).hom ≫
          (AlgebraicSimplex.sheafifiedSingularCochainsShiftedXIso R J P q r).inv) :=
  AlgebraicSimplex.sheafifiedSingularCochainsShiftIso_hom_f R J P q r

example {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (q : ℕ) :
    (AlgebraicSimplex.sheafifiedSingularCochainsFunctor R J q).map α ≫
        (AlgebraicSimplex.sheafifiedSingularCochainsShiftIso R J Q q).hom =
      (AlgebraicSimplex.sheafifiedSingularCochainsShiftIso R J P q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex (Sheaf J A) ℤ) (-(q : ℤ))).map
          ((AlgebraicSimplex.sheafifiedSingularCochainsFunctor R J 0).map α) :=
  AlgebraicSimplex.sheafifiedSingularCochainsShiftIso_naturality R J α q
