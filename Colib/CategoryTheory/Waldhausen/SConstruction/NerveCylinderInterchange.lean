/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderNaturality
public import Colib.Util.References

/-!
# The original two nerve-cylinder parameters commute with an identity action

An actual natural transformation between functors which preserve specified identity actions
commutes with their two original nerve-direction cylinders. The interval maps are independent;
the transformation and both endpoint action equations are retained literally.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial
universe u v u' v'
namespace CategoryTheory.Waldhausen

/-- The original cylinder object is selected by the specified nerve time. -/
@[colib_ref "quillen" "Quillen c561118b: NerveCylinderInterchange.lean:27"
  "adaptation" "Original two independent nerve parameters and unchanged endpoint actions."]
theorem nerveCylinderDiagram_obj {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {A B : Grid₂ n m ⥤ D} (η : A ⟶ B)
    (τ : m ⟶ ⦋1⦌) (p : Grid₂ n m) :
    (nerveCylinderDiagram η τ).obj p =
      ((ComposableArrows.mk₁ η).obj (τ.toOrderHom p.1)).obj p := rfl

/-- The original cylinder map is its actual crossing transformation followed by the endpoint map. -/
@[colib_ref "quillen" "Quillen c561118b: NerveCylinderInterchange.lean:34"
  "adaptation" "Original two independent nerve parameters and unchanged endpoint actions."]
theorem nerveCylinderDiagram_map {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {A B : Grid₂ n m ⥤ D} (η : A ⟶ B)
    (τ : m ⟶ ⦋1⦌) {p q : Grid₂ n m} (f : p ⟶ q) :
    (nerveCylinderDiagram η τ).map f =
      ((ComposableArrows.mk₁ η).map ((nerveTimeFunctor n τ).map f)).app p ≫
        ((ComposableArrows.mk₁ η).obj (τ.toOrderHom q.1)).map f := rfl


private theorem mk₁_whiskerLeft {K : Type*} [Category* K] {C : Type*} [Category* C]
    {D : Type*} [Category* D] (A : K ⥤ C) {F G : C ⥤ D} (η : F ⟶ G) :
    ComposableArrows.mk₁ (whiskerLeft A η) =
      ComposableArrows.mk₁ η ⋙ (whiskeringLeft K C D).obj A := by
  apply ComposableArrows.ext₁ (F := ComposableArrows.mk₁ (whiskerLeft A η))
    (G := ComposableArrows.mk₁ η ⋙ (whiskeringLeft K C D).obj A) rfl rfl
  simp

private theorem cylinder_whiskerLeft {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (η : F ⟶ G) {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ C) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft A η) τ =
      (nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj (ComposableArrows.mk₁ η) := by
  unfold nerveCylinderDiagram
  rw [mk₁_whiskerLeft]
  rfl

private theorem action_ordinal_interchange
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    {X Y : C} (f : X ⟶ Y) (a b c d : Fin 2) (hab : a ≤ b) (hcd : c ≤ d) :
    HEq
      (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app
          (((ComposableArrows.mk₁ α).obj a).obj X) ≫
        ((ComposableArrows.mk₁ η).obj d).map
          (((ComposableArrows.mk₁ α).map (homOfLE hab)).app X ≫
            ((ComposableArrows.mk₁ α).obj b).map f))
      (((ComposableArrows.mk₁ β).map (homOfLE hab)).app
          (((ComposableArrows.mk₁ η).obj c).obj X) ≫
        ((ComposableArrows.mk₁ β).obj b).map
          (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app X ≫
            ((ComposableArrows.mk₁ η).obj d).map f)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hab).elim
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hcd).elim
  all_goals
    simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ComposableArrows.mk₁_obj,
      ComposableArrows.Mk₁.obj, Functor.id_obj, Fin.mk_one, homOfLE_leOfHom,
      ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, Functor.id_map, Functor.map_comp,
      heq_eq_eq, NatTrans.id_app, Category.id_comp]
  exact β.naturality_assoc (η.app X) (G.map f)

/-- The actual two-time categorical cylinders commute when both endpoint functors preserve
exactly the specified source and target identity actions. -/
@[colib_ref "quillen" "Quillen c561118b: NerveCylinderInterchange.lean:88"
  "adaptation" "Original two independent nerve parameters and unchanged endpoint actions."]
theorem nerveCylinderDiagram_identityAction_interchange
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ C) (τ θ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (whiskerLeft (nerveCylinderDiagram (whiskerLeft A α) τ) η) θ =
      nerveCylinderDiagram
        (whiskerLeft (nerveCylinderDiagram (whiskerLeft A η) θ) β) τ := by
  simp only [cylinder_whiskerLeft]
  refine CategoryTheory.Functor.hext (fun p => ?_) ?_
  · dsimp [Functor.uncurry, Functor.prod', nerveTimeFunctor]
    generalize hτ : τ.toOrderHom p.1 = t
    generalize hθ : θ.toOrderHom p.1 = s
    fin_cases t <;> fin_cases s <;> rfl
  · intro p q f
    exact action_ordinal_interchange η α β hF hG (A.map f)
      (τ.toOrderHom p.1) (τ.toOrderHom q.1) (θ.toOrderHom p.1) (θ.toOrderHom q.1)
      (τ.toOrderHom.monotone (leOfHom f).1) (θ.toOrderHom.monotone (leOfHom f).1)

end CategoryTheory.Waldhausen
