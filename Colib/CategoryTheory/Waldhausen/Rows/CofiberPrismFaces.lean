/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.Rows.CofiberTwoPrism
public import Colib.CategoryTheory.Waldhausen.Rows.WeakObjectSimplex


/-! # Original weak-arrow faces of the actual cofiber prism

Each interval face retains its specified weak arrow: identity, original cofibration,
and original zero-to-quotient map obtained by gluing.
-/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/GrothendieckComparison/CofiberPrismFaces.lean`
   at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
   Original objects, maps, hypotheses and universe parameters are retained.
   Source-only preparation; native validation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The source face is the entire original weak-arrow square. -/
theorem cofiberTwoPrism_source_face :
    gridMap₂ (SimplexCategory.δ (2 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ = (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val := by
  have hobj : ∀ p, (gridMap₂ (SimplexCategory.δ (2 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ).obj p =
        (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val.obj p := by
    rintro ⟨t, ⟨⟨a, b⟩, hab⟩⟩
    change a.val ≤ b.val at hab
    fin_cases t <;> fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
      solve | omega | rfl
  refine CategoryTheory.Functor.ext hobj ?_
  rintro ⟨t, ⟨⟨a, b⟩, hab⟩⟩ ⟨s, ⟨⟨c, d⟩, hcd⟩⟩ f
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : t.val ≤ s.val ∧ a.val ≤ c.val ∧ b.val ≤ d.val := leOfHom f
  fin_cases t <;> fin_cases s <;> fin_cases a <;> fin_cases b <;>
    fin_cases c <;> fin_cases d <;> dsimp at hab hcd hf ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | have he : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      simp
    | simp only [cofiberTwoPrism, cofiberTwoWeakArrow, cofiberTwoRowComparison,
        cofiberTwoComparison, ComposableArrows.mk₁, Nat.reduceAdd, ComposableArrows.Mk₁.map,
        ComposableArrows.Mk₁.obj, Fin.zero_eta, Fin.isValue, Fin.mk_one, weakChainToGrid,
        homOfLE_leOfHom, SimplexCategory.δ, SimplexCategory.mkHom.eq_1, gridMap₂,
        SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq,
        SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply, interval, Monotone.functor_obj, homOfLE_refl,
        CategoryTheory.Functor.map_id, ObjectProperty.homMk_hom,
        cofiberTwoComparisonComponent, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.succAbove_ne_zero_zero, Subtype.mk.injEq, Prod.mk.injEq, Fin.succAbove_ne,
        and_false, ↓reduceDIte, zero_ne_one, and_self, eqToHom_refl, Category.id_comp,
        weakObjectSimplex, oneEmbedding, oneDiagram, oneIndex, oneChain, oneZeroToId,
        oneIdToZero, oneWeakArrow, Functor.comp_obj, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Nat.reduceMod, Functor.flip_obj_obj, ComposableArrows.precomp_obj,
        ComposableArrows.Precomp.obj_one, ComposableArrows.obj', Functor.id_obj,
        Functor.comp_map, Functor.flip_obj_map, ComposableArrows.precomp_map,
        ComposableArrows.Precomp.map_one_one, NatTrans.id_app, Functor.whiskerLeft_id',
        Category.comp_id]
      rfl

/-- The middle face is the entire original weak-arrow square. -/
theorem cofiberTwoPrism_middle_face :
    gridMap₂ (SimplexCategory.δ (1 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ = (W.weakObjectSimplex i hwi).val := by
  have hobj : ∀ p, (gridMap₂ (SimplexCategory.δ (1 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ).obj p = (W.weakObjectSimplex i hwi).val.obj p := by
    rintro ⟨t, ⟨⟨a, b⟩, hab⟩⟩
    change a.val ≤ b.val at hab
    fin_cases t <;> fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
      solve | omega | rfl
  refine CategoryTheory.Functor.ext hobj ?_
  rintro ⟨t, ⟨⟨a, b⟩, hab⟩⟩ ⟨s, ⟨⟨c, d⟩, hcd⟩⟩ f
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : t.val ≤ s.val ∧ a.val ≤ c.val ∧ b.val ≤ d.val := leOfHom f
  fin_cases t <;> fin_cases s <;> fin_cases a <;> fin_cases b <;>
    fin_cases c <;> fin_cases d <;> dsimp at hab hcd hf ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | have he : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      simp
    | simp only [cofiberTwoPrism, cofiberTwoWeakArrow, cofiberTwoRowComparison,
        cofiberTwoComparison, ComposableArrows.mk₁, Nat.reduceAdd, ComposableArrows.Mk₁.map,
        ComposableArrows.Mk₁.obj, Fin.zero_eta, Fin.isValue, Fin.mk_one, weakChainToGrid,
        homOfLE_leOfHom, SimplexCategory.δ, SimplexCategory.mkHom.eq_1, gridMap₂,
        SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq,
        SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply, interval, Monotone.functor_obj, homOfLE_refl,
        CategoryTheory.Functor.map_id, ObjectProperty.homMk_hom,
        cofiberTwoComparisonComponent, ne_eq, one_ne_zero, not_false_eq_true,
        Fin.succAbove_ne_zero_zero, Fin.one_succAbove_one, ↓reduceDIte, eqToHom_refl,
        Category.comp_id, Category.id_comp, weakObjectSimplex, oneEmbedding, oneDiagram,
        oneIndex, oneChain, oneZeroToId, oneIdToZero, oneWeakArrow, Functor.comp_obj,
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.reduceMod, Functor.flip_obj_obj,
        ComposableArrows.precomp_obj, ComposableArrows.Precomp.obj_one, ComposableArrows.obj',
        Functor.id_obj, Functor.comp_map, Functor.flip_obj_map, ComposableArrows.precomp_map,
        ComposableArrows.Precomp.map_one_one, NatTrans.id_app, Functor.whiskerLeft_app,
        Functor.flip_map_app, Functor.id_map]

/-- The quotient face is the entire original weak-arrow square. -/
theorem cofiberTwoPrism_quotient_face :
    gridMap₂ (SimplexCategory.δ (0 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ =
        (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val := by
  have hobj : ∀ p, (gridMap₂ (SimplexCategory.δ (0 : Fin 3)) (𝟙 ⦋1⦌) ⋙
      cofiberTwoPrism W i q hi hwi hQ).obj p =
        (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val.obj p := by
    rintro ⟨t, ⟨⟨a, b⟩, hab⟩⟩
    change a.val ≤ b.val at hab
    fin_cases t <;> fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
      solve | omega | rfl
  refine CategoryTheory.Functor.ext hobj ?_
  rintro ⟨t, ⟨⟨a, b⟩, hab⟩⟩ ⟨s, ⟨⟨c, d⟩, hcd⟩⟩ f
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : t.val ≤ s.val ∧ a.val ≤ c.val ∧ b.val ≤ d.val := leOfHom f
  fin_cases t <;> fin_cases s <;> fin_cases a <;> fin_cases b <;>
    fin_cases c <;> fin_cases d <;> dsimp at hab hcd hf ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | have he : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      simp

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/GrothendieckComparison/CofiberPrismFaces.lean:31-144" "adaptation"
  "The three complete grid-functor faces of the actual cofiber prism, including mixed maps:
    source identity, original inclusion and zero-to-quotient; no isomorphic row is substituted"]
  cofiberTwoPrism_source_face cofiberTwoPrism_middle_face cofiberTwoPrism_quotient_face

attribute [colib_ref "Waldhausen1985"
  "Section 1.3, definition of S_n C and face maps, pp. 328-329" "ingredient"
  "The literal S-construction with chosen-zero diagonal and displayed cofibration/pushout
    sequences, and its source, middle and quotient faces; the specific prism formulas are
    adapted from the pinned implementation"]
  cofiberTwoPrism_source_face cofiberTwoPrism_middle_face cofiberTwoPrism_quotient_face

end CategoryTheory.Waldhausen.Structure
