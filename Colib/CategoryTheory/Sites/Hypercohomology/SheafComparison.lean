/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.Basic

/-!
# Single-sheaf hypercohomology and the native ordinary Ext presheaf

Mathlib's `Ext.homAddEquiv` identifies the actual derived morphisms with Ext.
Here it is applied to Stacks' original free representing sheaf. The target is
the existing `FreeYonedaUnivLE.cohomologyPresheaf`, not a renamed copy.
Both restriction and coefficient maps are identified explicitly.

The degree-zero section equivalence and its naturality are already provided
by `FreeYonedaUnivLE.extSectionsAddEquiv` and are not redefined here.

## Implementation provenance

The comparison adapts
`kangxyz/aglib@2c34f185fa859e862661f939cd216b07bcccfb26`,
`Aglib/CategoryTheory/Sites/SheafCohomology/Large/Basic.lean`, and
`kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Large/Naturality.lean`.
The mathematical construction is directly Mathlib's Ext/derived-Hom comparison
on the native Stacks object.

Mazza--Voevodsky--Weibel, Lecture 12, Definition 12.11 and Lemma 12.12,
printed p. 92, give the Nisnevich free representing sheaf and ordinary-cohomology
comparison in a bounded-above context. They motivate this construction; the
present statement is the formal Ext comparison in the unbounded derived category,
not a new proof identifying all unbounded derived sections with derived Hom.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe w w' t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
  [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]

/-- Hypercohomology of a single sheaf is its native ordinary Ext cohomology. -/
@[colib_tag "COL-0304"]
def singleHypercohomologyEquivCohomology
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (X : C) :
    (hypercohomologyPresheaf J ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ)).obj
        (op X) ≃+ (cohomologyPresheaf.{w, t} F n).obj (op X) :=
  Ext.homAddEquiv.symm

/-- The comparison retains the original derived morphism. -/
@[simp]
theorem singleHypercohomologyEquivCohomology_hom
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) (X : C)
    (x : (hypercohomologyPresheaf J
      ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ)).obj (op X)) :
    (dsimp% only [Functor.op_obj]
      (singleHypercohomologyEquivCohomology J F n X x).hom) = x :=
  Ext.homAddEquiv.apply_symm_apply x

/-- The comparison commutes with the original restriction along a site morphism. -/
@[colib_tag "COL-0304"]
theorem singleHypercohomologyEquivCohomology_restriction
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (x : (hypercohomologyPresheaf J
      ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ)).obj (op Y)) :
    singleHypercohomologyEquivCohomology J F n X
        ((hypercohomologyPresheaf J
          ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ)).map f.op x) =
      (cohomologyPresheaf.{w, t} F n).map f.op
        (singleHypercohomologyEquivCohomology J F n Y x) := by
  change Ext.homEquiv.symm
      ((DerivedCategory.singleFunctor _ 0).map ((freeYoneda.{t} J).map f) ≫ x) =
    (Ext.mk₀ ((freeYoneda.{t} J).map f)).comp (Ext.homEquiv.symm x) (zero_add n)
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    Ext.hom, Equiv.apply_symm_apply]
  exact congrArg
    (fun y ↦ (DerivedCategory.singleFunctor _ 0).map ((freeYoneda.{t} J).map f) ≫ y)
    (Ext.homEquiv.apply_symm_apply x).symm

/-- The comparison commutes with the original morphism of coefficient sheaves. -/
@[colib_tag "COL-0304"]
theorem singleHypercohomologyEquivCohomology_coefficient
    {F G : Sheaf J AddCommGrpCat.{max v t}} (η : F ⟶ G) (n : ℕ) (X : C)
    (x : (hypercohomologyPresheaf J
      ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ)).obj (op X)) :
    singleHypercohomologyEquivCohomology J G n X
        (((hypercohomologyPresheafFunctor J (n : ℤ)).map
          ((CochainComplex.singleFunctor _ 0).map η)).app (op X) x) =
      ((cohomologyPresheafFunctor.{w, t} J n).map η).app (op X)
        (singleHypercohomologyEquivCohomology J F n X x) := by
  change Ext.homEquiv.symm (x ≫ ((DerivedCategory.singleFunctor _ 0).map η)⟦(n : ℤ)⟧') =
    (Ext.homEquiv.symm x).comp (Ext.mk₀ η) (add_zero n)
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    Ext.hom, Equiv.apply_symm_apply]
  exact congrArg (fun y ↦ y ≫ ((DerivedCategory.singleFunctor _ 0).map η)⟦(n : ℤ)⟧')
    (Ext.homEquiv.apply_symm_apply x).symm

end Stacks.Cohomology.FreeYonedaUnivLE

attribute [stacks 06XQ
  "single-sheaf specialization of derived Hom, with independent Ext universe"]
  Stacks.Cohomology.FreeYonedaUnivLE.singleHypercohomologyEquivCohomology

attribute [colib_ref "aglib"
  "Aglib/CategoryTheory/Sites/SheafCohomology/Large/Basic.lean: singleComparison"
  "adaptation"
  "Directly targets the native Stacks ordinary Ext presheaf without a compatibility alias"]
  Stacks.Cohomology.FreeYonedaUnivLE.singleHypercohomologyEquivCohomology

attribute [colib_ref "MVW2006"
  "Lecture 12, Definition 12.11 and Lemma 12.12, p. 92"
  "background"
  "Nisnevich free representables and Ext cohomology; the cited context is bounded above"]
  Stacks.Cohomology.FreeYonedaUnivLE.singleHypercohomologyEquivCohomology

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Large/Naturality.lean"
  "adaptation"
  "Original site restrictions and coefficient maps on native Stacks freeYoneda objects"]
  Stacks.Cohomology.FreeYonedaUnivLE.singleHypercohomologyEquivCohomology_restriction
  Stacks.Cohomology.FreeYonedaUnivLE.singleHypercohomologyEquivCohomology_coefficient
