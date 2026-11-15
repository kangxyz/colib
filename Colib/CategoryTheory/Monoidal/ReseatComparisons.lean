/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints

/-! # Tensorator and braiding comparisons under reseating -/

public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor.Monoidal

/-- Composing with the identity into the re-seated target and transporting along the right
unitor precomposes the original tensorator with the inverse comparison. -/
theorem transport_reseat_μ {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [mD : MonoidalCategory D] (F : C ⥤ D) [m : F.Monoidal]
    {T : D ⥤ D ⥤ D} {U : D} (e : curriedTensor D ≅ T) (ε : 𝟙_ D ≅ U) (X Y : C) :
    let A := reseat e ε
    let j := @reseatInverseMonoidal D _ mD _ _ e ε
    let g := @Functor.Monoidal.instComp C _ _ D _ mD D _ A F (𝟭 D) m j
    let r := @Functor.Monoidal.transport C _ _ D _ A (F ⋙ 𝟭 D) F g (Functor.rightUnitor F)
    @Functor.LaxMonoidal.μ C _ _ D _ A F r.toLaxMonoidal X Y =
      ((e.app (F.obj X)).app (F.obj Y)).inv ≫
        @Functor.LaxMonoidal.μ C _ _ D _ mD F m.toLaxMonoidal X Y := by
  intro A j g r
  let : MonoidalCategory D := A
  let p : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y) :=
    @Functor.LaxMonoidal.μ C _ _ D _ A (F ⋙ 𝟭 D) g.toLaxMonoidal X Y
  have h : @Functor.LaxMonoidal.μ C _ _ D _ A F r.toLaxMonoidal X Y =
      (𝟙 (F.obj X) ⊗ₘ 𝟙 (F.obj Y)) ≫ p ≫ 𝟙 (F.obj (X ⊗ Y)) :=
    @Functor.Monoidal.transport_μ C _ _ D _ A (F ⋙ 𝟭 D) F g (Functor.rightUnitor F) X Y
  have hi : 𝟙 (F.obj X) ⊗ₘ 𝟙 (F.obj Y) = 𝟙 (F.obj X ⊗ F.obj Y) :=
    id_tensorHom_id _ _
  exact (h.trans (congrArg (· ≫ p ≫ 𝟙 (F.obj (X ⊗ Y))) hi)).trans
    ((Category.id_comp _).trans ((Category.comp_id p).trans rfl))

end CategoryTheory.Functor.Monoidal

namespace CategoryTheory.MonoidalCategory

/-- A conjugation formula for the original braiding identifies the re-seated braiding when
its two comparison components are given. -/
theorem reseatSymmetric_braiding_hom_of_components {D : Type*} [Category* D]
    [MonoidalCategory D] [SymmetricCategory D] {T : D ⥤ D ⥤ D} {U : D}
    (e : curriedTensor D ≅ T) (ε : 𝟙_ D ≅ U) (X Y : D)
    (t : X ⊗ Y ≅ (T.obj X).obj Y) (t' : Y ⊗ X ≅ (T.obj Y).obj X)
    (b : (T.obj X).obj Y ⟶ (T.obj Y).obj X)
    (ht : (reseatIso e X Y).hom = t.hom) (ht' : (reseatIso e Y X).hom = t'.hom)
    (hβ : (β_ X Y).hom = t.hom ≫ b ≫ t'.inv) :
    (@BraidedCategory.braiding D _ (reseat e ε) (reseatSymmetric e ε).toBraidedCategory X Y).hom =
      b := by
  have hβ' : (β_ X Y).hom ≫ t'.hom = t.hom ≫ b :=
    t'.eq_comp_inv.mp (hβ.trans (Category.assoc _ _ _).symm)
  have hc : (reseatIso e X Y).hom ≫ 𝟙 ((T.obj X).obj Y) = t.hom :=
    (Category.comp_id _).trans ht
  have hc' : (reseatIso e Y X).hom ≫ 𝟙 ((T.obj Y).obj X) = t'.hom :=
    (Category.comp_id _).trans ht'
  have h := reseatSymmetric_braiding_comp_of_eq e ε (X := X) (Y := Y) b hc hc' hβ'
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp b))

end CategoryTheory.MonoidalCategory
