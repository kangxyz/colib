/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionArrowLaws
public import Colib.CategoryTheory.FiberedCategory.GrothendieckCocartesianMap
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! An independent prototype for restriction along an arbitrary change of index. -/
/-! Adapted from
`Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndex.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
universe u v w z u' v'
namespace CategoryTheory.SectionChangeIndex
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (K : C ⥤ D)

/-- The actual composite pseudofunctor. -/
def pullback : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'} :=
  K.toPseudofunctor.comp F

/-- Identity evaluation uses the original functor identity law. -/
theorem post_identity (c : C) :
    (Under.post K).obj (Under.mk (𝟙 c)) = Under.mk (𝟙 (K.obj c)) := by
  change Under.mk (K.map (𝟙 c)) = _
  rw [K.map_id]

/-- The underlying index restriction commutes strictly with reindexing. -/
theorem post_reindex {c d : C} (f : c ⟶ d) :
    Under.map f ⋙ Under.post K = Under.post K ⋙ Under.map (K.map f) := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j h => ?_)
  · change Under.mk (K.map (f ≫ i.hom)) = Under.mk (K.map f ≫ K.map i.hom)
    rw [K.map_comp]
  · ext
    simp

/-- Equality of index arrows retains the complete transported transition. -/
theorem transition_congr (c : D)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) c)
    {i j : Under c} (a b : i ⟶ j) (h : a = b) :
    originalArrowTransition F c s a =
      eqToHom (congrArg (fun t : i ⟶ j =>
        (F.map t.right.toLoc).toFunctor.obj ((originalEvaluationAt F c i).obj s)) h) ≫
        originalArrowTransition F c s b := by
  subst b
  simp

/-- Original section fibers, restricted along the full `Under.post K`. -/
def sectionFunctor (c : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)) :
    Under c ⥤ Pseudofunctor.Grothendieck (pullback F K) where
  obj i := ⟨i.right, (originalEvaluationAt F (K.obj c) ((Under.post K).obj i)).obj s⟩
  map f := ⟨f.right, originalArrowTransition F (K.obj c) s ((Under.post K).map f)⟩
  map_id i := by
    refine Pseudofunctor.Grothendieck.Hom.ext (F := pullback F K) _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp,
      Pseudofunctor.Grothendieck.categoryStruct_id_fiber]
    rw [transition_congr F (K.obj c) s _ _ ((Under.post K).map_id i),
      originalArrowTransition_id]
    simp [pullback, Pseudofunctor.comp, Functor.toPseudofunctor,
      PrelaxFunctor.map₂_eqToHom]
  map_comp f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext (F := pullback F K) _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp,
      Pseudofunctor.Grothendieck.categoryStruct_comp_fiber]
    rw [transition_congr F (K.obj c) s _ _ ((Under.post K).map_comp f g),
      originalArrowTransition_comp]
    dsimp [pullback, Pseudofunctor.comp, Functor.toPseudofunctor, Quiver.Hom.toLoc]
    simp only [PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans,
      eqToHom_app, Category.assoc]

/-- Restriction is literally a section over the new index category. -/
theorem sectionFunctor_comp (c : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)) :
    sectionFunctor F K c s ⋙ Pseudofunctor.Grothendieck.forget (pullback F K) =
      Under.forget c := rfl

/-- Original cocartesian transitions remain cocartesian after change of index. -/
def restrictedSection (c : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)) :
    underCocartesian (Pseudofunctor.Grothendieck.forget (pullback F K)) c :=
  ⟨⟨sectionFunctor F K c s, sectionFunctor_comp F K c s⟩, fun _ _ f => by
    have : IsIso ((sectionFunctor F K c s).map f).fiber :=
      CategoryTheory.GrothendieckSections.isIso_originalArrowTransition
        F (K.obj c) s
        ((Under.post K).map f)
    exact CategoryTheory.GrothendieckCocartesian.of_isIso_fiber
      ((sectionFunctor F K c s).map f)⟩
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
private theorem square_of_fiber_square {A B : D} (f : A ⟶ B)
    {a b : F.obj ⟨A⟩} {c d : F.obj ⟨B⟩} (α : a ⟶ b) (β : c ⟶ d)
    (p : (F.map f.toLoc).toFunctor.obj a ⟶ c)
    (q : (F.map f.toLoc).toFunctor.obj b ⟶ d)
    (h : (F.map f.toLoc).toFunctor.map α ≫ q = p ≫ β) :
    (CategoryTheory.GrothendieckFiber.inclusion F A).map α ≫
        (⟨f, q⟩ : (⟨A, b⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨B, d⟩) =
      (⟨f, p⟩ : (⟨A, a⟩ : Pseudofunctor.Grothendieck F) ⟶ ⟨B, c⟩) ≫
        (CategoryTheory.GrothendieckFiber.inclusion F B).map β := by
  refine Pseudofunctor.Grothendieck.Hom.ext (F := F) _ _ ?_ ?_
  · simp [CategoryTheory.GrothendieckFiber.inclusion]
  simp only [CategoryTheory.GrothendieckFiber.inclusion,
    Pseudofunctor.Grothendieck.categoryStruct_comp_fiber]
  simp only [Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor, Functor.id_obj,
    Pseudofunctor.Grothendieck.categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
    F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Functor.map_comp, Category.assoc, eqToHom_trans_assoc, F.mapComp_id_right_hom_app,
    Strict.rightUnitor_eqToIso, NatTrans.naturality_assoc, Functor.id_map,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  simp only [← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun k => _ ≫ k) h

/-- Every original vertical fiber map gives the unchanged vertical map of restricted sections. -/
def sectionMap (c : C)
    {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c)} (α : s ⟶ t) :
    sectionFunctor F K c s ⟶ sectionFunctor F K c t where
  app i := (CategoryTheory.GrothendieckFiber.inclusion (pullback F K) i.right).map
    ((originalEvaluationAt F (K.obj c) ((Under.post K).obj i)).map α)
  naturality {i k} f := by
    exact (square_of_fiber_square (pullback F K) f.right _ _ _ _
      (CategoryTheory.GrothendieckSections.originalArrowTransition_naturality
        F (K.obj c) α
        ((Under.post K).map f))).symm

/-- Restriction sends actual sections and their actual vertical maps to the fixed-base sections. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndex.lean:131"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
def underFunctor (c : C) :
    underCocartesian (Pseudofunctor.Grothendieck.forget F) (K.obj c) ⥤
      underCocartesian (Pseudofunctor.Grothendieck.forget (pullback F K)) c where
  obj := restrictedSection F K c
  map α := ObjectProperty.homMk ⟨sectionMap F K c α, by
    apply IsHomLift.of_fac'
      ((Functor.whiskeringRight (Under c)
        (Pseudofunctor.Grothendieck (pullback F K)) C).obj
          (Pseudofunctor.Grothendieck.forget (pullback F K)))
      (𝟙 (Under.forget c)) _ (sectionFunctor_comp F K c _) (sectionFunctor_comp F K c _)
    apply NatTrans.ext
    funext i
    simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
    rfl⟩
  map_id s := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply NatTrans.ext
    funext i
    simp [sectionMap]
    rfl
  map_comp α β := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    apply NatTrans.ext
    funext i
    simp [sectionMap]
    rfl


end CategoryTheory.SectionChangeIndex
