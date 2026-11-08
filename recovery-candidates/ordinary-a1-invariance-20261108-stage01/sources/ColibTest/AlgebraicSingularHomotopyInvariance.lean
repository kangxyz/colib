/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.HomotopyInvariance
import Mathlib.Data.ZMod.Basic

/-! # Actual ordinary interval homotopy-equivalence consumers -/

noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme AlgebraicSimplex
open scoped Simplicial

universe u v w

variable (R : Type u) [CommRing R]

example (U : SmoothSite (Spec (.of R))) :
    intervalInclusion R (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌)) 0 ≫
      intervalContraction R U =
        SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌) ≫
          intervalInclusion R U 0 :=
  intervalInclusion_zero_comp_intervalContraction R U

example (U : SmoothSite (Spec (.of (ZMod 6)))) :
    intervalInclusion (ZMod 6)
      (SmoothSite.product U ((cosimplicialSmoothSite (ZMod 6)).obj ⦋1⦌)) 1 ≫
        intervalContraction (ZMod 6) U = 𝟙 _ :=
  intervalInclusion_one_comp_intervalContraction (ZMod 6) U

variable {A : Type v} [Category.{w} A] [Preadditive A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

example (U : SmoothSite (Spec (.of R))) :
    Nonempty (_root_.HomotopyEquiv
      ((((evaluation _ A).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((singularChainsFunctor R).obj P))
      ((((evaluation _ A).obj
        (op (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌)))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj ((singularChainsFunctor R).obj P))) :=
  ⟨ordinaryIntervalHomotopyEquiv R P U⟩

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (ordinaryIntervalHomotopyEquiv R P U).hom.f n =
      P.map (SmoothSite.productMap
        (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌))
          (𝟙 ((cosimplicialSmoothSite R).obj ⦋n⦌))).op := rfl

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (ordinaryIntervalHomotopyEquiv R P U).inv.f n =
      P.map (SmoothSite.productMap (intervalInclusion R U 0)
        (𝟙 ((cosimplicialSmoothSite R).obj ⦋n⦌))).op := rfl

example (U : SmoothSite (Spec (.of R))) :
    Nonempty (_root_.Homotopy
      ((ordinaryIntervalHomotopyEquiv R P U).hom ≫
        (ordinaryIntervalHomotopyEquiv R P U).inv) (𝟙 _)) :=
  ⟨(ordinaryIntervalHomotopyEquiv R P U).homotopyHomInvId⟩

example (U : SmoothSite (Spec (.of R))) :
    Nonempty (_root_.Homotopy
      ((ordinaryIntervalHomotopyEquiv R P U).inv ≫
        (ordinaryIntervalHomotopyEquiv R P U).hom) (𝟙 _)) :=
  ⟨(ordinaryIntervalHomotopyEquiv R P U).homotopyInvHomId⟩

variable [CategoryWithHomology A]

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (ordinaryIntervalHomologyIso R P U n).hom =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation _ A).map
            (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌)).op)
              (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n :=
  ordinaryIntervalHomologyIso_hom R P U n

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (ordinaryIntervalHomologyIso R P U n).inv =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((evaluation _ A).map (intervalInclusion R U 0).op)
          (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n := rfl

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map
          (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌)).op)
            (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n) :=
  isIso_ordinaryInterval_homologyMap R P U n
