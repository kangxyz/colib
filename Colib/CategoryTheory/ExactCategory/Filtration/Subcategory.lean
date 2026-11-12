/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Abelian.Devissage.Filtration
public import Colib.CategoryTheory.Abelian.Subcategory.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Lifting actual filtrations into a subquotient-closed abelian category

Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/Subcategory.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.ExactCategory.ExactStructure.Filtration
variable {C : Type u} [Category.{v} C] [Abelian C]
  {P : ObjectProperty C} (Q : ObjectProperty C)
  [Q.ContainsZero] [Q.IsClosedUnderSubobjects] [Q.IsClosedUnderQuotients]
  [Q.IsClosedUnderFiniteProducts]

/-- Every stage of a filtration of an object in a subquotient-closed
subcategory lies in that category. The actual short exact maps are retained. -/
def toFullSubcategory {X : C} (F : (abelianExactStructure C).Filtration P X) (hX : Q X) :
    (abelianExactStructure Q.FullSubcategory).Filtration (P.inverseImage Q.ι) ⟨X, hX⟩ := by
  induction F with
  | zero h =>
    refine .zero ?_
    rw [IsZero.iff_id_eq_zero]
    apply ObjectProperty.hom_ext
    exact h.eq_of_src _ _
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    have := hS'.mono_f
    have := hS'.epi_g
    have h₁ : Q S.X₁ := Q.prop_of_mono S.f hX
    have h₃ : Q S.X₃ := Q.prop_of_epi S.g hX
    let T : ShortComplex Q.FullSubcategory :=
      ShortComplex.mk (Q.homMk S.f : ⟨S.X₁, h₁⟩ ⟶ ⟨S.X₂, hX⟩)
        (Q.homMk S.g : ⟨S.X₂, hX⟩ ⟶ ⟨S.X₃, h₃⟩) (by ext; exact S.zero)
    have hT : T.ShortExact := CategoryTheory.ShortExact.reflects_shortExact_of_faithful Q.ι hS'
    exact .step T hT (ih h₁) hP

end CategoryTheory.ExactCategory.ExactStructure.Filtration
