/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Devissage.Filtration
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Transport of finite filtrations along endpoint isomorphisms

Adapted from Quillen's `Filtration/Refinement.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual short complex maps.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.ExactCategory.ExactStructure.Filtration
variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}
/-- Transport a filtration along an actual isomorphism of its endpoint. -/
def ofIso {X Y : C} (F : (abelianExactStructure C).Filtration P X) (e : X ≅ Y) :
    (abelianExactStructure C).Filtration P Y := by
  cases F with
  | zero h => exact .zero (h.of_iso e.symm)
  | step S hS F hP =>
    let T := ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) (by simp)
    have et : S ≅ T := ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp [T]) (by simp [T])
    exact .step T (ShortComplex.shortExact_of_iso et hS) F hP

end CategoryTheory.ExactCategory.ExactStructure.Filtration
