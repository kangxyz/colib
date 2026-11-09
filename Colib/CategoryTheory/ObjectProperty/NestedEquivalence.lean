/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Original evaluation equivalences restricted through nested full subcategories

A property inside a full subcategory is flattened without changing its original objects or
morphisms. Restricting an existing evaluation equivalence and then flattening retains the
original evaluation functor. This isolates categorical restriction from large geometric models.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.ObjectProperty
variable {D : Type u} [Category.{v} D] (P Q : CategoryTheory.ObjectProperty D) (hQP : Q ≤ P)

/-- Flatten actual nested full-subcategory objects and their unchanged original arrows. -/
def nestedEquivalence : (Q.inverseImage P.ι).FullSubcategory ≌ Q.FullSubcategory where
  functor :=
    { obj X := ⟨X.obj.obj, X.property⟩
      map f := CategoryTheory.ObjectProperty.homMk f.hom.hom }
  inverse :=
    { obj X := ⟨⟨X.obj, hQP _ X.property⟩, X.property⟩
      map f := CategoryTheory.ObjectProperty.homMk (CategoryTheory.ObjectProperty.homMk f.hom) }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- Flattening retains the literal original object. -/
theorem nestedEquivalence_obj (X : (Q.inverseImage P.ι).FullSubcategory) :
    ((nestedEquivalence P Q hQP).functor.obj X).obj = X.obj.obj := rfl

/-- Flattening retains the literal original morphism. -/
theorem nestedEquivalence_map {X Y : (Q.inverseImage P.ι).FullSubcategory} (f : X ⟶ Y) :
    ((nestedEquivalence P Q hQP).functor.map f).hom = f.hom.hom := rfl

variable {C : Type u'} [Category.{v'} C] (e : C ≌ P.FullSubcategory)
    (R : CategoryTheory.ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    (h : (Q.inverseImage P.ι).inverseImage e.functor = R)

/-- Restrict the original evaluation equivalence and flatten its existing target objects. -/
def evaluationRestrictionEquivalence : R.FullSubcategory ≌ Q.FullSubcategory :=
  (e.congrFullSubcategory h).trans (nestedEquivalence P Q hQP)

/-- The forward restriction is the original evaluation lifted through the target property. -/
theorem evaluationRestrictionEquivalence_functor
    (hR : ∀ X : R.FullSubcategory, Q ((e.functor.obj X.obj).obj)) :
    (evaluationRestrictionEquivalence P Q hQP e R h).functor =
      Q.lift (R.ι ⋙ e.functor ⋙ P.ι) hR := rfl

/-- The restricted equivalence retains the original forward evaluation on objects. -/
theorem evaluationRestrictionEquivalence_obj (X : R.FullSubcategory) :
    ((evaluationRestrictionEquivalence P Q hQP e R h).functor.obj X).obj =
      (e.functor.obj X.obj).obj := rfl

/-- The restricted equivalence retains the original forward evaluation on every morphism. -/
theorem evaluationRestrictionEquivalence_map {X Y : R.FullSubcategory} (f : X ⟶ Y) :
    ((evaluationRestrictionEquivalence P Q hQP e R h).functor.map f).hom =
      (e.functor.map f.hom).hom := rfl

end CategoryTheory.ObjectProperty
