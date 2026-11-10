/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ProjectiveCorepresented
public import Colib.CategoryTheory.Sites.Hypercohomology.Basic

/-!
# Evaluating unbounded hypercohomology at a projective free representing sheaf

For a site object whose native Stacks free representing sheaf
is projective, hypercohomology is the cohomology of the literal sections
complex. We use Mathlib's `sheafSections`, Stacks' `sectionsAddEquiv`, and
the projectively corepresented comparison. No second sections functor,
representing sheaf, Hom complex or cohomology presheaf is introduced.

The site object and morphism universes are independent, with coefficients in
`max u v t` and an independent derived universe. Stacks
`coyonedaIsoSections` requires `SmallCategory`, so the necessary natural
isomorphism below extends that interface to this universe range.
The projectivity hypothesis is supplied geometrically by the field consumer;
it is not a user-supplied version of the comparison conclusion.

Implementation provenance: motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/Evaluation.lean` and
`EvaluationNaturality.lean`. All integer degrees and actual cochain maps are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.Corepresented

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v t}]

/-- The native free representing sheaf corepresents sections with independent site universes. -/
def coyonedaIsoSheafSections (X : C) :
    preadditiveCoyoneda.obj (op ((freeYoneda.{max u t} J).obj X)) ≅
      (sheafSections J AddCommGrpCat.{max u v t}).obj (op X) :=
  NatIso.ofComponents (fun F ↦ (sectionsAddEquiv X F).toAddCommGrpIso) (by
    intro F G f
    ext (α : (freeYoneda.{max u t} J).obj X ⟶ F)
    exact sectionsEquiv_naturality X α f)

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max u v t})]
  (X : C) [Projective ((freeYoneda.{max u t} J).obj X)]

/-- Hypercohomology at a projective free representing sheaf is literal section cohomology. -/
def hypercohomologyEvaluationAddEquiv
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ) (n : ℤ) :
    (hypercohomologyPresheaf.{w, max u t} J K n).obj (op X) ≃+
      ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).mapHomologicalComplex
        (.up ℤ)).obj K).homology n := by
  letI : ((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).Additive :=
    Functor.additive_of_iso (coyonedaIsoSheafSections.{t} J X)
  exact (projectiveHomologyDerivedAddEquiv _ ((freeYoneda.{max u t} J).obj X)
    (coyonedaIsoSheafSections.{t} J X) K n).symm

/-- The evaluation comparison preserves the map of the actual coefficient complex. -/
theorem hypercohomologyEvaluationAddEquiv_naturality
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ} (f : K ⟶ L)
    (n : ℤ) (x : (hypercohomologyPresheaf.{w, max u t} J K n).obj (op X)) :
    hypercohomologyEvaluationAddEquiv.{w, t} J X L n
        (((hypercohomologyPresheafFunctor.{w, max u t} J n).map f).app (op X) x) =
      HomologicalComplex.homologyMap
        ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).mapHomologicalComplex
          (.up ℤ)).map f) n (hypercohomologyEvaluationAddEquiv.{w, t} J X K n x) := by
  let : ((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).Additive :=
    Functor.additive_of_iso (coyonedaIsoSheafSections.{t} J X)
  let E (M : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ) :=
    projectiveHomologyDerivedAddEquiv _ ((freeYoneda.{max u t} J).obj X)
      (coyonedaIsoSheafSections.{t} J X) M n
  change (E L).symm (x ≫ (DerivedCategory.Q.map f)⟦n⟧') =
    HomologicalComplex.homologyMap
      ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).mapHomologicalComplex
        (.up ℤ)).map f) n ((E K).symm x)
  apply (E L).injective
  calc
    E L ((E L).symm (x ≫ (DerivedCategory.Q.map f)⟦n⟧')) =
        x ≫ (DerivedCategory.Q.map f)⟦n⟧' := (E L).apply_symm_apply _
    _ = E K ((E K).symm x) ≫ (DerivedCategory.Q.map f)⟦n⟧' :=
      congrArg (fun y ↦ y ≫ (DerivedCategory.Q.map f)⟦n⟧') ((E K).apply_symm_apply x).symm
    _ = E L (HomologicalComplex.homologyMap
        ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).mapHomologicalComplex
          (.up ℤ)).map f) n ((E K).symm x)) :=
      (projectiveHomologyDerivedAddEquiv_naturality _ ((freeYoneda.{max u t} J).obj X)
        (coyonedaIsoSheafSections.{t} J X) f n ((E K).symm x)).symm

end Stacks.Cohomology.FreeYonedaUnivLE

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/Evaluation.lean:101-108"
  "adaptation" "Independent site universes, native freeYoneda and sheafSections, unbounded target"]
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyEvaluationAddEquiv

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/EvaluationNaturality.lean:107-124"
  "adaptation" "Actual coefficient-map naturality with independent site universes"]
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyEvaluationAddEquiv_naturality

attribute [colib_tag "COL-0394"]
  Stacks.Cohomology.FreeYonedaUnivLE.coyonedaIsoSheafSections
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyEvaluationAddEquiv
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyEvaluationAddEquiv_naturality
