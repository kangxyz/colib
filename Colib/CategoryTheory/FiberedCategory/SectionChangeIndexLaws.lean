/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndex

/-! Exact evaluation and reindexing laws of the independent change-index prototype. -/
/-! Adapted from
`Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexLaws.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open CategoryTheory.GrothendieckFiber
universe u v w z u' v'
namespace CategoryTheory.SectionChangeIndex
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (K : C ⥤ D)

/-- Every fiber evaluation retains the entire original vertical map. -/
theorem evaluationAt_map (c : C) (i : Under c)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)} (f : s ⟶ t) :
    (originalEvaluationAt (pullback F K) c i).map ((underFunctor F K c).map f) =
      (originalEvaluationAt F (K.obj c) ((Under.post K).obj i)).map f := by
  change (fromFiber (pullback F K) i.right).map
    ((cocartesianEvaluation (Pseudofunctor.Grothendieck.forget (pullback F K))
      (Under.forget c) i).map ((underFunctor F K c).map f)) = _
  apply (toFiber (pullback F K) i.right).map_injective
  rw [toFiber_map_fromFiber_map]
  apply Subtype.ext
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Exact evaluation at any original index, not only at identity. -/
theorem evaluationAt (c : C) (i : Under c) :
    underFunctor F K c ⋙ originalEvaluationAt (pullback F K) c i =
      originalEvaluationAt F (K.obj c) ((Under.post K).obj i) := by
  fapply CategoryTheory.Functor.ext
  · intro s
    rfl
  · intro s t f
    simpa only [Functor.comp_obj, Functor.comp_map, eqToHom_refl,
      Category.id_comp, Category.comp_id] using evaluationAt_map F K c i f

/-- Identity evaluation commutes exactly, with the original `K.map_id` transport. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexLaws.lean:49"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem evaluation (c : C) :
    underFunctor F K c ⋙ originalEvaluation (pullback F K) c =
      originalEvaluation F (K.obj c) := by
  have h := evaluationAt F K c (Under.mk (𝟙 c))
  have hi := congrArg
    (fun a : K.obj c ⟶ K.obj c =>
      (show underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c) ⥤
        F.obj ⟨K.obj c⟩ from originalEvaluationAt F (K.obj c) (Under.mk a)))
    (K.map_id c)
  exact h.trans hi

/-- Restriction is an equivalence because both original evaluation functors are equivalences. -/
instance restriction_isEquivalence (c : C) : (underFunctor F K c).IsEquivalence := by
  have : (underFunctor F K c ⋙ originalEvaluation (pullback F K) c).IsEquivalence := by
    rw [evaluation]
    infer_instance
  exact Functor.isEquivalence_of_comp_right (underFunctor F K c)
    (originalEvaluation (pullback F K) c)


private theorem grothHom_heq {B : Type*} [Category* B]
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{v', u'})
    {x y x' y' : Pseudofunctor.Grothendieck P} (hx : x = x') (hy : y = y')
    (a : x ⟶ y) (b : x' ⟶ y') (hb : HEq a.base b.base) (hf : HEq a.fiber b.fiber) :
    HEq a b := by
  subst x'; subst y'
  cases a; cases b
  cases eq_of_heq hb
  cases eq_of_heq hf
  rfl

private theorem transition_index_heq {J : Type*} [Category* J] (c : D)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) c)
    (L M : J ⥤ Under c) (e : L = M) {i j : J} (a : i ⟶ j) :
    HEq (originalArrowTransition F c s (L.map a))
      (originalArrowTransition F c s (M.map a)) := by
  subst M
  rfl

/-- The objects of the reindexed section agree without replacing a lift. -/
theorem sectionFunctor_reindex_obj {c d : C} (f : c ⟶ d)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)) (i : Under d) :
    (sectionFunctor F K d
        ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (K.map f)).obj s)).obj i =
      (sectionFunctor F K c s).obj ((Under.map f).obj i) := by
  dsimp [sectionFunctor, originalEvaluationAt, underCocartesianReindex,
    cocartesianReindex, cocartesianEvaluation, fiberEvaluation, reindex]
  simp only [K.map_comp]
  rfl

/-- The whole underlying section commutes with the exact index restriction. -/
theorem sectionFunctor_reindex {c d : C} (f : c ⟶ d)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)) :
    sectionFunctor F K d
        ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (K.map f)).obj s) =
      Under.map f ⋙ sectionFunctor F K c s := by
  apply CategoryTheory.Functor.hext (sectionFunctor_reindex_obj F K f s)
  intro i j a
  apply grothHom_heq (pullback F K)
    (sectionFunctor_reindex_obj F K f s i) (sectionFunctor_reindex_obj F K f s j)
  · rfl
  · exact transition_index_heq F (K.obj c) s _ _ (post_reindex K f).symm a

private theorem sectionHom_heq {B : Type*} [Category* B] {E : Type*} [Category* E]
    (π : E ⥤ B) (c : B) {s t s' t' : underCocartesian π c}
    (hs : s = s') (ht : t = t') (a : s ⟶ t) (b : s' ⟶ t')
    (h : ∀ i, HEq (a.hom.val.app i) (b.hom.val.app i)) : HEq a b := by
  subst s'; subst t'
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  apply NatTrans.ext
  funext i
  exact eq_of_heq (h i)

private theorem evaluationMap_congr {E : Type*} [Category* E] {c d : D}
    (I : F.obj ⟨d⟩ ⥤ E) (a b : c ⟶ d) (h : a = b)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) c} (α : s ⟶ t) :
    HEq (I.map ((originalEvaluationAt F c (Under.mk a)).map α))
      (I.map ((originalEvaluationAt F c (Under.mk b)).map α)) := by
  subst b
  rfl

/-- The actual section functors form a strict natural transformation. -/
theorem reindex_naturality {c d : C} (f : c ⟶ d) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (K.map f) ⋙
        underFunctor F K d =
      underFunctor F K c ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget (pullback F K)) f := by
  have ho (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)) :
      (underFunctor F K d).obj
        ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (K.map f)).obj s) =
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget (pullback F K)) f).obj
        ((underFunctor F K c).obj s) := by
    apply ObjectProperty.FullSubcategory.ext
    apply Subtype.ext
    exact sectionFunctor_reindex F K f s
  apply CategoryTheory.Functor.hext ho
  intro s t a
  apply sectionHom_heq _ d (ho s) (ho t)
  intro i
  exact evaluationMap_congr F (inclusion (pullback F K) i.right)
    (K.map f ≫ K.map i.hom) (K.map (f ≫ i.hom)) (K.map_comp f i.hom).symm a

end CategoryTheory.SectionChangeIndex
