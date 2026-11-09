/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.StrictSections
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Cocartesian sections of actual categories over a base and literal restriction of indices. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
namespace CategoryTheory.StrictSections
variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {J : Type u₃} [Category.{v₃} J] {K : Type u₄} [Category.{v₄} K]
  (π : E ⥤ C) (q : J ⥤ C)

/-- Every transition in the section is an actual cocartesian lift of its base arrow. -/
def cocartesian : ObjectProperty (StrictSections π q) := fun s =>
  ∀ ⦃i j : J⦄ (f : i ⟶ j), π.IsStronglyCocartesian (q.map f) (s.1.map f)

/-- The existing full subcategory retains precisely the cocartesian sections. -/
abbrev CocartesianSections := (cocartesian π q).FullSubcategory

/-- Restriction retains the actual cocartesian lifts; no new lift is chosen. -/
def cocartesianReindex (H : K ⥤ J) :
    CocartesianSections π q ⥤ CocartesianSections π (H ⋙ q) :=
  (cocartesian π (H ⋙ q)).lift ((cocartesian π q).ι ⋙ reindex π q H)
    (fun s _ _ f => s.property (H.map f))

/-- Evaluation remembers the actual original fiber of a cocartesian section. -/
def cocartesianEvaluation (j : J) : CocartesianSections π q ⥤ Functor.Fiber π (q.obj j) :=
  (cocartesian π q).ι ⋙ fiberEvaluation π q j

/-- Cocartesian sections over the coslice of a base object. -/
abbrev underCocartesian (X : C) := CocartesianSections π (Under.forget X)

/-- Reindex the actual cocartesian sections along a base morphism. -/
def underCocartesianReindex {X Y : C} (f : X ⟶ Y) :
    underCocartesian π X ⥤ underCocartesian π Y :=
  cocartesianReindex π (Under.forget X) (Under.map f)

/-- Evaluation at the original identity arrow. -/
def underCocartesianEvaluation (X : C) :
    underCocartesian π X ⥤ Functor.Fiber π X :=
  cocartesianEvaluation π (Under.forget X) (Under.mk (𝟙 X))

private theorem lift_congr {A : Type*} [Category* A] {B : Type*} [Category* B]
    (P : ObjectProperty B) {F G : A ⥤ B} (h : F = G)
    (hF : ∀ a, P (F.obj a)) (hG : ∀ a, P (G.obj a)) : P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- Restriction along an identity is literally the identity on cocartesian sections. -/
theorem underCocartesianReindex_id (X : C) :
    underCocartesianReindex π (𝟙 X) = 𝟭 (underCocartesian π X) := by
  change (cocartesian π (Under.forget X)).lift
    ((cocartesian π (Under.forget X)).ι ⋙ underReindex π (𝟙 X)) _ =
    (cocartesian π (Under.forget X)).lift (cocartesian π (Under.forget X)).ι
      (fun s => s.property)
  apply lift_congr
  exact congrArg (fun F => (cocartesian π (Under.forget X)).ι ⋙ F) (underReindex_id π X)

/-- Restriction along a composite is the literal composite on cocartesian sections. -/
theorem underCocartesianReindex_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    underCocartesianReindex π (f ≫ g) =
      underCocartesianReindex π f ⋙ underCocartesianReindex π g := by
  change (cocartesian π (Under.forget Z)).lift
    ((cocartesian π (Under.forget X)).ι ⋙ underReindex π (f ≫ g)) _ =
    (cocartesian π (Under.forget Z)).lift
      ((cocartesian π (Under.forget X)).ι ⋙ underReindex π f ⋙ underReindex π g) _
  apply lift_congr
  exact congrArg (fun F => (cocartesian π (Under.forget X)).ι ⋙ F)
    (underReindex_comp π f g)

end CategoryTheory.StrictSections
