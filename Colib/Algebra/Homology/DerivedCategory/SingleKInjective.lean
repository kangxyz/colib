/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Linear.Basic

/-! # Maps from single complexes to K-injective complexes -/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace Stacks.Cohomology.Corepresented

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The actual shifted Hom from a single complex into a K-injective complex. -/
def singleKInjectiveHomAddEquiv (P : A) (I : CochainComplex A ℤ)
    [I.IsKInjective] (n : ℤ) :
    ((HomotopyCategory.quotient A (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj P) ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj (I⟦n⟧)) ≃+
      ((DerivedCategory.singleFunctor A 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj P))
      (I⟦n⟧))).trans <|
    (CategoryTheory.Linear.homCongr ℤ ((DerivedCategory.singleFunctorIsoCompQh A 0).symm.app P)
      (((DerivedCategory.quotientCompQhIso A).app (I⟦n⟧)) ≪≫
        (DerivedCategory.Q.commShiftIso n).app I)).toAddEquiv

/-- The comparison preserves precomposition by the original single-complex map. -/
theorem singleKInjectiveHomAddEquiv_precomp {P P' : A} (f : P' ⟶ P)
    (I : CochainComplex A ℤ) [I.IsKInjective] (n : ℤ)
    (x : (HomotopyCategory.quotient A (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj P) ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj (I⟦n⟧)) :
    singleKInjectiveHomAddEquiv P' I n
        ((HomotopyCategory.quotient A (.up ℤ)).map ((CochainComplex.singleFunctor A 0).map f) ≫
          x) =
      (DerivedCategory.singleFunctor A 0).map f ≫ singleKInjectiveHomAddEquiv P I n x := by
  let Q := HomotopyCategory.quotient A (.up ℤ)
  let S := CochainComplex.singleFunctor A 0
  let D := DerivedCategory.singleFunctor A 0
  let F := DerivedCategory.Qh (C := A)
  let e := (DerivedCategory.singleFunctorIsoCompQh A 0).symm
  let d := (DerivedCategory.quotientCompQhIso A).app (I⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app I
  have he : D.map f ≫ e.inv.app P = e.inv.app P' ≫ F.map (Q.map (S.map f)) :=
    e.inv.naturality f
  change (e.inv.app P' ≫ F.map (Q.map (S.map f) ≫ x)) ≫ d.hom =
    D.map f ≫ ((e.inv.app P ≫ F.map x) ≫ d.hom)
  calc
    _ = (e.inv.app P' ≫ F.map (Q.map (S.map f)) ≫ F.map x) ≫ d.hom :=
      congrArg (fun g => (e.inv.app P' ≫ g) ≫ d.hom) (F.map_comp (Q.map (S.map f)) x)
    _ = ((e.inv.app P' ≫ F.map (Q.map (S.map f))) ≫ F.map x) ≫ d.hom :=
      congrArg (· ≫ d.hom) (Category.assoc _ _ _).symm
    _ = ((D.map f ≫ e.inv.app P) ≫ F.map x) ≫ d.hom :=
      congrArg (fun g => (g ≫ F.map x) ≫ d.hom) he.symm
    _ = _ := by simp only [Category.assoc]

end Stacks.Cohomology.Corepresented
