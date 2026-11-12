/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.Evaluation
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Colib.Algebra.Homology.HomotopyCategory.CorepresentedPrecomposition

/-!
# Evaluating hypercohomology on a K-injective coefficient complex

The degreewise sections of a K-injective cochain complex compute the native
hypercohomology of that complex in every integer degree. Restriction of
sections along a site morphism corresponds to precomposition by its map
of free representing sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.Corepresented

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

section Localization

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

private def singleLocalizationIso :
    CochainComplex.singleFunctor A 0 ⋙
        (HomotopyCategory.quotient A (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      DerivedCategory.singleFunctor A 0 :=
  Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ A 0).symm

private def singleKInjectiveHomAddEquiv (P : A) (I : CochainComplex A ℤ)
    [I.IsKInjective] (n : ℤ) :
    ((HomotopyCategory.quotient A (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj P) ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj (I⟦n⟧)) ≃+
      ((DerivedCategory.singleFunctor A 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj P))
      (I⟦n⟧))).trans <|
    (CategoryTheory.Linear.homCongr ℤ ((singleLocalizationIso (A := A)).app P)
      (((DerivedCategory.quotientCompQhIso A).app (I⟦n⟧)) ≪≫
        (DerivedCategory.Q.commShiftIso n).app I)).toAddEquiv

private theorem singleKInjectiveHomAddEquiv_precomp {P P' : A} (f : P' ⟶ P)
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
  let e := singleLocalizationIso (A := A)
  let d := (DerivedCategory.quotientCompQhIso A).app (I⟦n⟧) ≪≫
    (DerivedCategory.Q.commShiftIso n).app I
  have he : D.map f ≫ e.inv.app P = e.inv.app P' ≫ F.map (Q.map (S.map f)) :=
    e.inv.naturality f
  change (e.inv.app P' ≫ F.map (Q.map (S.map f) ≫ x)) ≫ d.hom =
    D.map f ≫ ((e.inv.app P ≫ F.map x) ≫ d.hom)
  calc
    _ = (e.inv.app P' ≫ F.map (Q.map (S.map f)) ≫ F.map x) ≫ d.hom := by
      rw [F.map_comp]
    _ = ((e.inv.app P' ≫ F.map (Q.map (S.map f))) ≫ F.map x) ≫ d.hom :=
      congrArg (· ≫ d.hom) (Category.assoc _ _ _).symm
    _ = ((D.map f ≫ e.inv.app P) ≫ F.map x) ≫ d.hom :=
      congrArg (fun g => (g ≫ F.map x) ≫ d.hom) he.symm
    _ = _ := by simp only [Category.assoc]

end Localization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v t}]

private theorem coyonedaIsoSheafSections_naturality_left {X Y : C} (f : X ⟶ Y) :
    (coyonedaIsoSheafSections.{t} J Y).hom ≫
        (sheafSections J AddCommGrpCat.{max u v t}).map f.op =
      preadditiveCoyoneda.map ((freeYoneda.{max u t} J).map f).op ≫
        (coyonedaIsoSheafSections.{t} J X).hom := by
  apply NatTrans.ext
  funext F
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro (α : (freeYoneda.{max u t} J).obj Y ⟶ F)
  exact (sectionsEquiv_naturality_left f F α).symm

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max u v t})]

/-- Literal section cohomology of a K-injective coefficient complex computes
its native hypercohomology in every integer degree. -/
@[no_expose]
def kInjectiveEvaluationAddEquiv (X : C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ) [I.IsKInjective] (n : ℤ) :
    ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).mapHomologicalComplex
        (.up ℤ)).obj I).homology n ≃+
      (hypercohomologyPresheaf.{w, max u t} J I n).obj (op X) := by
  let T := (sheafSections J AddCommGrpCat.{max u v t}).obj (op X)
  let P := (freeYoneda.{max u t} J).obj X
  let e := coyonedaIsoSheafSections.{t} J X
  let : T.Additive := Functor.additive_of_iso e
  exact (corepresentedHomologyHomotopyAddEquiv T P e I n).trans
    (singleKInjectiveHomAddEquiv P I n)

/-- The K-injective evaluation comparison carries literal restriction of sections
to restriction along the actual map of free representing sheaves. -/
theorem kInjectiveEvaluationAddEquiv_naturality {X Y : C} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ) [I.IsKInjective] (n : ℤ)
    (x : ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op Y)).mapHomologicalComplex
      (.up ℤ)).obj I).homology n) :
    kInjectiveEvaluationAddEquiv.{w, t} J X I n
        (HomologicalComplex.homologyMap
          ((((sheafSections J AddCommGrpCat.{max u v t}).map f.op).mapHomologicalComplex
            (.up ℤ)).app I) n x) =
      (hypercohomologyPresheaf.{w, max u t} J I n).map f.op
        (kInjectiveEvaluationAddEquiv.{w, t} J Y I n x) := by
  let A := Sheaf J AddCommGrpCat.{max u v t}
  let P := freeYoneda.{max u t} J
  let T := sheafSections J AddCommGrpCat.{max u v t}
  let eX := coyonedaIsoSheafSections.{t} J X
  let eY := coyonedaIsoSheafSections.{t} J Y
  let : (T.obj (op X)).Additive := Functor.additive_of_iso eX
  let : (T.obj (op Y)).Additive := Functor.additive_of_iso eY
  let EX := singleKInjectiveHomAddEquiv (P.obj X) I n
  let EY := singleKInjectiveHomAddEquiv (P.obj Y) I n
  let y := corepresentedHomologyHomotopyAddEquiv _ (P.obj Y) eY I n x
  let ρ := ((T.map f.op).mapHomologicalComplex (.up ℤ)).app I
  change EX (corepresentedHomologyHomotopyAddEquiv _ (P.obj X) eX I n
      (HomologicalComplex.homologyMap ρ n x)) =
    (DerivedCategory.singleFunctor A 0).map (P.map f) ≫ EY y
  have h := corepresentedHomologyHomotopyAddEquiv_precomp eY eX (P.map f) (T.map f.op)
    (coyonedaIsoSheafSections_naturality_left.{t} J f) I n x
  exact (congrArg EX h).trans (singleKInjectiveHomAddEquiv_precomp (P.map f) I n y)

end Stacks.Cohomology.FreeYonedaUnivLE
