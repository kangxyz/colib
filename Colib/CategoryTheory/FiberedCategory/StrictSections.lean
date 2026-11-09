/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! Strict sections of a category over a base, using the existing fiber category. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {J : Type u₃} [Category.{v₃} J] {K : Type u₄} [Category.{v₄} K]

/-- Actual functors over a fixed base diagram; morphisms are vertical natural transformations. -/
abbrev StrictSections (π : E ⥤ C) (q : J ⥤ C) :=
  Functor.Fiber ((Functor.whiskeringRight J E C).obj π) q

namespace StrictSections
variable (π : E ⥤ C) (q : J ⥤ C)

/-- Restrict a section and its vertical morphisms along an actual index functor. -/
def reindex (H : K ⥤ J) : StrictSections π q ⥤ StrictSections π (H ⋙ q) where
  obj s := ⟨H ⋙ s.1, by
    change H ⋙ (s.1 ⋙ π) = H ⋙ q
    exact congrArg (fun F : J ⥤ C => H ⋙ F) s.2⟩
  map {s t} a := ⟨Functor.whiskerLeft H a.1, by
    apply IsHomLift.of_fac'
      ((Functor.whiskeringRight K E C).obj π) (𝟙 (H ⋙ q)) _
      (by change H ⋙ (s.1 ⋙ π) = H ⋙ q; exact congrArg (fun F : J ⥤ C => H ⋙ F) s.2)
      (by change H ⋙ (t.1 ⋙ π) = H ⋙ q; exact congrArg (fun F : J ⥤ C => H ⋙ F) t.2)
    apply NatTrans.ext
    funext k
    have ha := a.2
    have h := IsHomLift.fac' ((Functor.whiskeringRight J E C).obj π) (𝟙 q) a.1
    have hk := congrArg (fun α => α.app (H.obj k)) h
    simpa using hk⟩
  map_id s := by apply Subtype.ext; rfl
  map_comp a b := by apply Subtype.ext; rfl

private theorem reindex_map_heq (H H' : K ⥤ J) (h : H = H')
    {s t : StrictSections π q} (a : s ⟶ t) :
    HEq ((reindex π q H).map a) ((reindex π q H').map a) := by
  subst h
  rfl

/-- Evaluation retains the actual object and morphism in the total category. -/
def evaluation (j : J) : StrictSections π q ⥤ E :=
  Functor.Fiber.fiberInclusion ⋙ (CategoryTheory.evaluation J E).obj j

/-- Sections over all arrows out of a fixed base object. -/
abbrev under (X : C) := StrictSections π (Under.forget X)

/-- Literal precomposition of coslice indices. -/
def underReindex {X Y : C} (f : X ⟶ Y) : under π X ⥤ under π Y :=
  reindex π (Under.forget X) (Under.map f)

/-- The original evaluation in the total category at the identity arrow. -/
def underEvaluation (X : C) : under π X ⥤ E :=
  evaluation π (Under.forget X) (Under.mk (𝟙 X))

/-- Reindexing by an identity is the literal identity functor. -/
theorem underReindex_id (X : C) : underReindex π (𝟙 X) = 𝟭 (under π X) := by
  apply Functor.hext
  · intro s
    apply Subtype.ext
    change Under.map (𝟙 X) ⋙ s.1 = s.1
    rw [Under.mapId_eq]
    rfl
  · intro s t a
    exact reindex_map_heq π (Under.forget X) _ _ (Under.mapId_eq X) a

/-- Reindexing by a composite is the literal composite functor. -/
theorem underReindex_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    underReindex π (f ≫ g) = underReindex π f ⋙ underReindex π g := by
  apply Functor.hext
  · intro s
    apply Subtype.ext
    change Under.map (f ≫ g) ⋙ s.1 = Under.map g ⋙ Under.map f ⋙ s.1
    rw [Under.mapComp_eq]
    rfl
  · intro s t a
    exact reindex_map_heq π (Under.forget X) _ _ (Under.mapComp_eq f g) a

/-- Evaluation lands in the actual original fiber, retaining vertical components. -/
def fiberEvaluation (j : J) : StrictSections π q ⥤ Functor.Fiber π (q.obj j) where
  obj s := ⟨s.1.obj j, congrArg (fun F : J ⥤ C => F.obj j) s.2⟩
  map {s t} a := ⟨a.1.app j, by
    apply IsHomLift.of_fac' π (𝟙 (q.obj j)) _
      (congrArg (fun F : J ⥤ C => F.obj j) s.2)
      (congrArg (fun F : J ⥤ C => F.obj j) t.2)
    have ha := a.2
    have h := IsHomLift.fac' ((Functor.whiskeringRight J E C).obj π) (𝟙 q) a.1
    simpa using congrArg (fun α => α.app j) h⟩
  map_id s := by apply Subtype.ext; rfl
  map_comp a b := by apply Subtype.ext; rfl

end StrictSections
end CategoryTheory
