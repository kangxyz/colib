/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# Occupied extension coordinates followed by a single-complex projection

This source-only candidate preserves the native extension coordinate maps until
the corresponding inverse pairs are cancelled. It has not been elaborated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace HomologicalComplex

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]

/-- In an occupied degree, the inverse map/extension comparison followed by
two extended maps and the native single projection is the original composite. -/
theorem map_extend_single_component
    (F : C ⥤ D) [F.Additive]
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (h : e.f (0 : ℕ) = (0 : ℤ))
    (K : ChainComplex C ℕ) (L : ChainComplex D ℕ) (A : D)
    (α : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶ L)
    (β : L ⟶ (single D (ComplexShape.down ℕ) 0).obj A) :
    F.map (K.extendXIso e h).inv ≫
      (Stacks.DerivedIndexing.mapExtendIso F e K).inv.f 0 ≫
      (extendMap α e).f 0 ≫
      (extendMap β e).f 0 ≫
      (extendSingleIso e A 0 0 h).hom.f 0 ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 A).hom =
        α.f 0 ≫ β.f 0 ≫ (singleObjXSelf (ComplexShape.down ℕ) 0 A).hom := by
  rw [Stacks.DerivedIndexing.mapExtendIso_inv_f_eq F e K h,
    extendMap_f α e h, extendMap_f β e h,
    extendSingleIso_hom_f e A 0 0 h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

end HomologicalComplex
