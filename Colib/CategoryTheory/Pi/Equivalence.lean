/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Pi.FiniteStages
public import Colib.CategoryTheory.SmallModel.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Coordinate equivalences on the canonical finite-support family

A family of equivalences restricts the existing `Equivalence.pi` to the same finite-support
full subcategories. Actual `IsZero` support is preserved exactly. The original evaluation
squares are literal functor equalities, and singleton insertion squares use the original
coordinate equivalences and the unique isomorphisms between zero objects off support.
With additive coordinate equivalences, both directions are exact.

The intended upstream module is `Aglib.CategoryTheory.Pi.Equivalence`. Its current consumer is
small-model transport of Quillen's primary-module decomposition. The chosen model universe is
an explicit parameter: no comparison of topological K-groups across universes is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v₁ v₂ w₁ w₂ t

open CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Pi

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

section Equivalences

variable {I : Type u} {C : I → Type v₁} {D : I → Type v₂}
  [∀ i, Category.{w₁} (C i)] [∀ i, Category.{w₂} (D i)]
  [∀ i, Abelian (C i)] [∀ i, Abelian (D i)] (e : ∀ i, C i ≌ D i)

/-- Coordinate equivalences preserve the actual nonzero-support set. -/
theorem equivalencePi_support (M : ∀ i, C i) :
    {i | ¬ IsZero ((Equivalence.pi e).functor.obj M i)} = {i | ¬ IsZero (M i)} := by
  ext i
  apply not_congr
  constructor
  · exact IsZero.of_full_of_faithful_of_isZero (e i).functor _
  · exact (e i).functor.map_isZero

/-- Finite support is the literal inverse image under the original coordinatewise equivalence. -/
theorem finiteObjectSupport_inverseImage :
    (finiteObjectSupport D).inverseImage (Equivalence.pi e).functor = finiteObjectSupport C := by
  funext M
  exact propext (by
    change {i | ¬ IsZero ((Equivalence.pi e).functor.obj M i)}.Finite ↔
      {i | ¬ IsZero (M i)}.Finite
    rw [equivalencePi_support e M])

/-- Restrict the original product equivalence to the same canonical finite-support categories. -/
def finiteCategoryFamilyEquivalence : FiniteCategoryFamily C ≌ FiniteCategoryFamily D :=
  (Equivalence.pi e).congrFullSubcategory (finiteObjectSupport_inverseImage e)

/-- The restricted equivalence retains the original ambient coordinatewise functor. -/
theorem finiteCategoryFamilyEquivalence_comp_inclusion :
    (finiteCategoryFamilyEquivalence e).functor ⋙ (finiteObjectSupport D).ι =
      (finiteObjectSupport C).ι ⋙ (Equivalence.pi e).functor := rfl

/-- Evaluation of the restricted equivalence is the original coordinate equivalence. -/
theorem finiteCategoryFamilyEquivalence_comp_evaluation (i : I) :
    (finiteCategoryFamilyEquivalence e).functor ⋙ (finiteCategoryEvaluation D i).toFunctor =
      (finiteCategoryEvaluation C i).toFunctor ⋙ (e i).functor := rfl

/-- The actual support set is unchanged, including arbitrary zero representatives. -/
theorem finiteCategoryFamilyEquivalence_support (M : FiniteCategoryFamily C) :
    {i | ¬ IsZero (((finiteCategoryFamilyEquivalence e).functor.obj M).obj i)} =
      {i | ¬ IsZero (M.obj i)} :=
  equivalencePi_support e M.obj

/-- The original singleton square, after evaluation at any actual coordinate. -/
def finiteCategoryFamilySingletonEvaluationIso (i j : I) :
    singletonInclusion C i ⋙ (finiteCategoryFamilyEquivalence e).functor ⋙
        (finiteCategoryEvaluation D j).toFunctor ≅
      (e i).functor ⋙ singletonInclusion D i ⋙ (finiteCategoryEvaluation D j).toFunctor := by
  by_cases h : j = i
  · subst j
    exact eqToIso (by
      rw [finiteCategoryFamilyEquivalence_comp_evaluation,
        singletonInclusion_comp_evaluation, ← Functor.assoc,
        singletonInclusion_comp_evaluation]
      simp only [Functor.id_comp, Functor.comp_id])
  · refine NatIso.ofComponents (fun X => ?_) ?_
    · exact ((e j).functor.map_isZero (singletonInclusion_obj_isZero C i j h X)).iso
        (singletonInclusion_obj_isZero D i j h ((e i).functor.obj X))
    · intro X Y f
      exact ((e j).functor.map_isZero (singletonInclusion_obj_isZero C i j h X)).eq_of_src _ _

/-- Singleton insertion commutes with the same coordinatewise family equivalence. -/
def finiteCategoryFamilySingletonIso (i : I) :
    singletonInclusion C i ⋙ (finiteCategoryFamilyEquivalence e).functor ≅
      (e i).functor ⋙ singletonInclusion D i := by
  let e' : (singletonInclusion C i ⋙ (finiteCategoryFamilyEquivalence e).functor) ⋙
      (finiteObjectSupport D).ι ≅
      ((e i).functor ⋙ singletonInclusion D i) ⋙ (finiteObjectSupport D).ι :=
    NatIso.pi' (fun j => finiteCategoryFamilySingletonEvaluationIso e i j)
  exact NatIso.ofComponents (fun X => (finiteObjectSupport D).isoMk (e'.app X)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact e'.hom.naturality f)

variable [∀ i, (e i).functor.Additive]

instance finiteCategoryFamilyEquivalence_functor_additive :
    (finiteCategoryFamilyEquivalence e).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    funext i
    exact (e i).functor.map_add

/-- The original restricted coordinatewise equivalence is exact. -/
def finiteCategoryFamilyExactFunctor : ExactCategory.ExactFunctor
    (finiteCategoryExactStructure C) (finiteCategoryExactStructure D) where
  toFunctor := (finiteCategoryFamilyEquivalence e).functor
  map_conflation _ hS := hS.map_of_exact _

/-- The original restricted inverse coordinate equivalences are exact. -/
def finiteCategoryFamilyInverseExactFunctor : ExactCategory.ExactFunctor
    (finiteCategoryExactStructure D) (finiteCategoryExactStructure C) where
  toFunctor := (finiteCategoryFamilyEquivalence e).inverse
  additive := (finiteCategoryFamilyEquivalence e).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

end Equivalences

section SmallModels

variable {I : Type u} (C : I → Type v₁) [∀ i, Category.{w₁} (C i)]
  [∀ i, Abelian (C i)] [∀ i, EssentiallySmall.{t} (C i)]

/-- The coordinatewise chosen small models use the explicitly supplied common model universe. -/
def finiteFamilySmallModelEquivalence : FiniteCategoryFamily C ≌
    FiniteCategoryFamily (fun i => SmallModel.{t} (C i)) :=
  finiteCategoryFamilyEquivalence (fun i => equivSmallModel.{t} (C i))

/-- Exactness of the original chosen coordinatewise small-model functors. -/
def finiteFamilyToSmallModelExactFunctor : ExactCategory.ExactFunctor
    (finiteCategoryExactStructure C)
    (finiteCategoryExactStructure (fun i => SmallModel.{t} (C i))) :=
  finiteCategoryFamilyExactFunctor (fun i => equivSmallModel.{t} (C i))

/-- Exactness of the same chosen coordinatewise realization functors. -/
def finiteFamilyFromSmallModelExactFunctor : ExactCategory.ExactFunctor
    (finiteCategoryExactStructure (fun i => SmallModel.{t} (C i)))
    (finiteCategoryExactStructure C) :=
  finiteCategoryFamilyInverseExactFunctor (fun i => equivSmallModel.{t} (C i))

end SmallModels

end CategoryTheory.Pi
