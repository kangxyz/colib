/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionEvaluation

/-!
# Fullness of original cocartesian-section evaluation

The strong cocartesian universal property extends any original vertical identity component uniquely
through the whole coslice. It proves naturality and recovers the supplied component under
evaluation.
The existence of a section over a prescribed fiber object is a separate assertion.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.StrictSections
variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
  (π : E ⥤ C) (R : C) {s t : underCocartesian π R}
  (f : (underCocartesianEvaluation π R).obj s ⟶ (underCocartesianEvaluation π R).obj t)

/-- The identity-evaluation morphism with its actual section-object endpoints explicit. -/
abbrev identityComponent :
    s.obj.val.obj (Under.mk (𝟙 R)) ⟶ t.obj.val.obj (Under.mk (𝟙 R)) := f.val

/-- The component forced by the actual cocartesian universal property. -/
def extendComponent (j : Under R) : s.obj.val.obj j ⟶ t.obj.val.obj j := by
  have hs : π.IsStronglyCocartesian j.hom (s.obj.val.map (initialArrow R j)) :=
    s.property (initialArrow R j)
  have ht : π.IsStronglyCocartesian j.hom (t.obj.val.map (initialArrow R j)) :=
    t.property (initialArrow R j)
  have hf : π.IsHomLift (𝟙 R) (identityComponent π R f) := f.property
  have hft : π.IsHomLift j.hom ((identityComponent π R f) ≫ t.obj.val.map (initialArrow R j)) :=
    IsHomLift.comp_lift_id_left π j.hom (t.obj.val.map (initialArrow R j)) (identityComponent π R f)
  exact Functor.IsStronglyCocartesian.map π j.hom (s.obj.val.map (initialArrow R j))
    (g := 𝟙 j.right) (Category.comp_id j.hom).symm
    ((identityComponent π R f) ≫ t.obj.val.map (initialArrow R j))

instance instIsHomLiftExtendComponent (j : Under R) :
    π.IsHomLift (𝟙 j.right) (extendComponent π R f j) := by
  have hs : π.IsStronglyCocartesian j.hom (s.obj.val.map (initialArrow R j)) :=
    s.property (initialArrow R j)
  have ht : π.IsStronglyCocartesian j.hom (t.obj.val.map (initialArrow R j)) :=
    t.property (initialArrow R j)
  have hf : π.IsHomLift (𝟙 R) (identityComponent π R f) := f.property
  have hft : π.IsHomLift j.hom ((identityComponent π R f) ≫ t.obj.val.map (initialArrow R j)) :=
    IsHomLift.comp_lift_id_left π j.hom (t.obj.val.map (initialArrow R j)) (identityComponent π R f)
  exact Functor.IsStronglyCocartesian.map_isHomLift π j.hom
    (s.obj.val.map (initialArrow R j)) (g := 𝟙 j.right) (Category.comp_id j.hom).symm
    (identityComponent π R f ≫ t.obj.val.map (initialArrow R j))

/-- The extended component factors the literal identity-component map and original transition. -/
theorem extendComponent_fac (j : Under R) :
    s.obj.val.map (initialArrow R j) ≫ extendComponent π R f j =
      (identityComponent π R f) ≫ t.obj.val.map (initialArrow R j) := by
  have hs : π.IsStronglyCocartesian j.hom (s.obj.val.map (initialArrow R j)) :=
    s.property (initialArrow R j)
  have ht : π.IsStronglyCocartesian j.hom (t.obj.val.map (initialArrow R j)) :=
    t.property (initialArrow R j)
  have hf : π.IsHomLift (𝟙 R) (identityComponent π R f) := f.property
  have hft : π.IsHomLift j.hom ((identityComponent π R f) ≫ t.obj.val.map (initialArrow R j)) :=
    IsHomLift.comp_lift_id_left π j.hom (t.obj.val.map (initialArrow R j)) (identityComponent π R f)
  exact Functor.IsStronglyCocartesian.fac π j.hom (s.obj.val.map (initialArrow R j))
    (g := 𝟙 j.right) (Category.comp_id j.hom).symm
    ((identityComponent π R f) ≫ t.obj.val.map (initialArrow R j))

/-- The original coslice transition starts from the original identity component. -/
theorem initialArrow_comp {i j : Under R} (a : i ⟶ j) :
    initialArrow R i ≫ a = initialArrow R j := by
  ext
  exact a.w

/-- The uniquely extended components commute with every original section transition. -/
theorem extendComponent_naturality {i j : Under R} (a : i ⟶ j) :
    s.obj.val.map a ≫ extendComponent π R f j =
      extendComponent π R f i ≫ t.obj.val.map a := by
  have hs : π.IsStronglyCocartesian i.hom (s.obj.val.map (initialArrow R i)) :=
    s.property (initialArrow R i)
  have hsa : π.IsStronglyCocartesian a.right (s.obj.val.map a) := s.property a
  have hta : π.IsStronglyCocartesian a.right (t.obj.val.map a) := t.property a
  apply Functor.IsStronglyCocartesian.ext π i.hom
    (s.obj.val.map (initialArrow R i)) a.right
  calc
    s.obj.val.map (initialArrow R i) ≫ s.obj.val.map a ≫ extendComponent π R f j =
        s.obj.val.map (initialArrow R j) ≫ extendComponent π R f j := by
          rw [← Category.assoc, ← Functor.map_comp, initialArrow_comp]
    _ = (identityComponent π R f) ≫ t.obj.val.map (initialArrow R j) := extendComponent_fac π R f j
    _ = (identityComponent π R f) ≫ t.obj.val.map (initialArrow R i) ≫ t.obj.val.map a := by
          rw [← Functor.map_comp, initialArrow_comp]
    _ = s.obj.val.map (initialArrow R i) ≫ extendComponent π R f i ≫ t.obj.val.map a := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ t.obj.val.map a) (extendComponent_fac π R f i).symm

/-- The full natural transformation forced by an original vertical identity component. -/
def extendNatTrans : s.obj.val ⟶ t.obj.val where
  app := extendComponent π R f
  naturality {i j} a := extendComponent_naturality π R f (i := i) (j := j) a

/-- The original universal extension is a vertical transformation of actual sections. -/
def extend : s ⟶ t :=
  ObjectProperty.homMk ⟨extendNatTrans π R f, by
    apply IsHomLift.of_fac' ((Functor.whiskeringRight (Under R) E C).obj π)
      (𝟙 (Under.forget R)) _ s.obj.property t.obj.property
    apply NatTrans.ext
    funext j
    have h := IsHomLift.fac' π (𝟙 j.right) (extendComponent π R f j)
    simpa [extendNatTrans] using h⟩

/-- Evaluation of the extended transformation recovers the original component. -/
theorem evaluation_extend : (underCocartesianEvaluation π R).map (extend π R f) = f := by
  apply Subtype.ext
  have h := extendComponent_fac π R f (Under.mk (𝟙 R))
  have hi : initialArrow R (Under.mk (𝟙 R)) = 𝟙 (Under.mk (𝟙 R)) := rfl
  change extendComponent π R f (Under.mk (𝟙 R)) = (identityComponent π R f)
  simp only [hi, Functor.map_id] at h
  exact (Category.id_comp _).symm.trans (h.trans (Category.comp_id _))

/-- Every original vertical identity component extends, without assuming an evaluation inverse. -/
instance : (underCocartesianEvaluation π R).Full where
  map_surjective f := ⟨extend π R f, evaluation_extend π R f⟩

end CategoryTheory.StrictSections
