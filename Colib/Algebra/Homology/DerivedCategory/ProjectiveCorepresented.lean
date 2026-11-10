/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.Homology.Ext.CorepresentedHomComplex

/-!
# Unbounded cohomology of a projectively corepresented functor

Let `T : A ⥤ AddCommGrpCat` be corepresented by a projective object `Z` of an
abelian category. For every integer-indexed complex `K`, the cohomology of the
literal degreewise complex `T(K)` identifies with `Hom(Z[0], Q(K)[n])`.
The comparison is natural in the actual coefficient cochain map.

The Hom-complex comparison and its naturality are the existing Stacks
`corepresentedHomologyHomotopyAddEquiv`. The additional step uses Mathlib's
K-projective localization theorem for the single complex `Z[0]`. The target
complex is unbounded and need not be K-injective. No enough-projectives or
enough-injectives hypothesis is used; the derived-category universe is independent.

This extracts the categorical argument of
`Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/Evaluation.lean:38-49`
and `EvaluationNaturality.lean:85-97` at motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`, while reusing the existing Stacks
Hom-complex API rather than recreating it. The module-specialized comparison
in Stacks `Homology/HomComplex/RHom.lean` has a different hypothesis range.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Cohomology.Corepresented

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] (Z : A) [Projective Z]
  (e : preadditiveCoyoneda.obj (op Z) ≅ T)

/-- A projectively corepresented additive functor computes derived Hom on every complex. -/
def projectiveHomologyDerivedAddEquiv (K : CochainComplex A ℤ) (n : ℤ) :
    ((T.mapHomologicalComplex (.up ℤ)).obj K).homology n ≃+
      ((DerivedCategory.singleFunctor A 0).obj Z ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  let P := (CochainComplex.singleFunctor A 0).obj Z
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P 0
  exact (corepresentedHomologyHomotopyAddEquiv T Z e K n).trans <|
    (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
      (CochainComplex.IsKProjective.Qh_map_bijective P _)).trans <|
      (CategoryTheory.Linear.homCongr ℤ
        (((DerivedCategory.quotientCompQhIso A).app P) ≪≫
          ((DerivedCategory.singleFunctorIsoCompQ A 0).app Z).symm)
        (((DerivedCategory.quotientCompQhIso A).app (K⟦n⟧)) ≪≫
          (DerivedCategory.Q.commShiftIso n).app K)).toAddEquiv

/-- The comparison sends a class to its localized homotopy morphism, with canonical shifts. -/
theorem projectiveHomologyDerivedAddEquiv_apply (K : CochainComplex A ℤ) (n : ℤ)
    (x : ((T.mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    projectiveHomologyDerivedAddEquiv T Z e K n x =
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app Z).hom ≫
        ((DerivedCategory.quotientCompQhIso A).app
          ((CochainComplex.singleFunctor A 0).obj Z)).inv ≫
        DerivedCategory.Qh.map (corepresentedHomologyHomotopyAddEquiv T Z e K n x) ≫
        ((DerivedCategory.quotientCompQhIso A).app (K⟦n⟧)).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K := by
  change
    ((((DerivedCategory.singleFunctorIsoCompQ A 0).app Z).hom ≫
      ((DerivedCategory.quotientCompQhIso A).app
        ((CochainComplex.singleFunctor A 0).obj Z)).inv) ≫
      DerivedCategory.Qh.map (corepresentedHomologyHomotopyAddEquiv T Z e K n x)) ≫
      (((DerivedCategory.quotientCompQhIso A).app (K⟦n⟧)).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K) = _
  simp only [Category.assoc]

/-- Coefficient maps correspond to postcomposition by their actual shifted localization. -/
theorem projectiveHomologyDerivedAddEquiv_naturality {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (n : ℤ)
    (x : ((T.mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    projectiveHomologyDerivedAddEquiv T Z e L n
        (HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map f) n x) =
      projectiveHomologyDerivedAddEquiv T Z e K n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  have h := ConcreteCategory.congr_hom
    (corepresentedHomologyHomotopyIso_hom_naturality T Z e f n) x
  change corepresentedHomologyHomotopyAddEquiv T Z e L n
      (HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map f) n x) =
    corepresentedHomologyHomotopyAddEquiv T Z e K n x ≫
      (HomotopyCategory.quotient A (.up ℤ)).map (f⟦n⟧') at h
  rw [projectiveHomologyDerivedAddEquiv_apply, h,
    projectiveHomologyDerivedAddEquiv_apply]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom,
    DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    Functor.commShiftIso_hom_naturality]

end Stacks.Cohomology.Corepresented

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/Evaluation.lean:38-49"
  "adaptation" "K-projective localization of a projective corepresenting single complex"]
  Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/EvaluationNaturality.lean:85-97"
  "adaptation" "Naturality in actual coefficient cochain maps, with canonical localization shifts"]
  Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv_naturality

attribute [colib_tag "COL-0394"]
  Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv
  Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv_apply
  Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv_naturality

attribute [colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/Homology/Ext/CorepresentedHomComplex.lean:72-99,104-135"
  "ingredient" "Native corepresented Hom-complex comparison and coefficient naturality"]
  Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv
