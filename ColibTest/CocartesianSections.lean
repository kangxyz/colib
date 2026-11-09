/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.FiberedCategory.CocartesianSectionTransition
import Colib.CategoryTheory.FiberedCategory.GrothendieckZeroSections
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# Consumers of actual cocartesian sections

Arbitrary pseudofunctors exercise actual canonical objects, vertical morphisms,
essential surjectivity, literal coslice restriction and chosen zeros. A constant
abelian-group pseudofunctor additionally retains distinct endomorphisms of the
integers, so the evaluation equivalence is tested on a nontrivial fiber.
-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections

noncomputable section
namespace ColibTest.CocartesianSections

universe u v u' v'
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

example (x : F.obj ⟨R⟩) (j : Under R) :
    ((cocartesianSection F R x).obj.val.obj j).fiber =
      (F.map j.hom.toLoc).toFunctor.obj x := rfl

/-- A genuine two-arrow coefficient route retains the actual composite pullback component. -/
example {S T : C} (f : R ⟶ S) (g : S ⟶ T) (x : F.obj ⟨R⟩) :
    (((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj
      (cocartesianSection F R x)).obj.val.obj (Under.mk g)).fiber =
        (F.map (f ≫ g).toLoc).toFunctor.obj x := rfl

example (x : F.obj ⟨R⟩) :
    Nonempty ((originalEvaluation F R).obj (cocartesianSection F R x) ≅ x) :=
  ⟨originalEvaluationSectionIso F R x⟩

example {s t : underCocartesian (Pseudofunctor.Grothendieck.forget F) R} :
    Function.Bijective (fun a : s ⟶ t => (originalEvaluation F R).map a) :=
  ⟨(originalEvaluation F R).map_injective, (originalEvaluation F R).map_surjective⟩

example (x : F.obj ⟨R⟩) :
    ∃ s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R,
      Nonempty ((originalEvaluation F R).obj s ≅ x) :=
  ⟨cocartesianSection F R x, ⟨originalEvaluationSectionIso F R x⟩⟩

example : underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (𝟙 R) =
    𝟭 (underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :=
  underCocartesianReindex_id _ _

example {S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g) =
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g :=
  underCocartesianReindex_comp _ _ _

example (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) (j : Under R) :
    IsIso (originalTransition F R s j) := inferInstance

example {S : C} (f : R ⟶ S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
      originalEvaluation F S = originalEvaluationAt F R (Under.mk f) :=
  originalEvaluation_reindex F R f

variable (z : ∀ R : C, F.obj ⟨R⟩) (hz : ∀ R, IsZero (z R))
  (hm : ∀ {R S : C} (f : R ⟶ S), IsZero ((F.map f.toLoc).toFunctor.obj (z R)))

example : (originalEvaluation F R).obj
    (GrothendieckZeroSections.sectionZero F z hz hm R) = z R := rfl

example {S : C} (f : R ⟶ S) :
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj
      (GrothendieckZeroSections.sectionZero F z hz hm R) =
        GrothendieckZeroSections.sectionZero F z hz hm S := rfl

example : IsZero (GrothendieckZeroSections.sectionZero F z hz hm R) :=
  GrothendieckZeroSections.isZero_sectionZero F z hz hm R

/-- A constant pseudofunctor with the nontrivial category of abelian groups as fiber. -/
def abelianGroups : Pseudofunctor (LocallyDiscrete (Type)) Cat :=
  pseudofunctorOfIsLocallyDiscrete
    (fun _ => Cat.of AddCommGrpCat)
    (fun _ => (𝟭 AddCommGrpCat).toCatHom)
    (fun _ => Iso.refl _)
    (fun _ _ => Iso.refl _)

/-- The canonical section contains the original integer group at every base arrow. -/
def integerSection := cocartesianSection abelianGroups Bool (AddCommGrpCat.of ℤ)

/-- Identity and zero remain different after passage to the actual section category. -/
example : (𝟙 integerSection : integerSection ⟶ integerSection) ≠
    (originalEvaluation abelianGroups Bool).preimage
      ((originalEvaluationSectionIso abelianGroups Bool (AddCommGrpCat.of ℤ)).hom ≫
        (0 : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) ≫
        (originalEvaluationSectionIso abelianGroups Bool (AddCommGrpCat.of ℤ)).inv) := by
  intro h
  let i : AddCommGrpCat.of ℤ ≅ AddCommGrpCat.of ℤ :=
    originalEvaluationSectionIso abelianGroups Bool (AddCommGrpCat.of ℤ)
  have h' := congrArg ((originalEvaluation abelianGroups Bool).map) h
  have hz := (originalEvaluation abelianGroups Bool).map_preimage
    (X := integerSection) (Y := integerSection)
    (i.hom ≫ (0 : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) ≫ i.inv)
  have hZ : (𝟙 (AddCommGrpCat.of ℤ)) =
      i.hom ≫ (0 : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) ≫ i.inv :=
    ((originalEvaluation abelianGroups Bool).map_id integerSection).symm.trans (h'.trans hz)
  have hZ' : (𝟙 (AddCommGrpCat.of ℤ)) = 0 := hZ.trans (by simp)
  exact Int.one_ne_zero (ConcreteCategory.congr_hom hZ' (1 : ℤ))

end ColibTest.CocartesianSections
