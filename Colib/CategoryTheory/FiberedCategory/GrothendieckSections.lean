/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.GrothendieckCocartesian
public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiber
public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionFullness

/-!
# Original pseudofunctor objects give actual cocartesian sections

The section at an arrow is its original pseudofunctor image. All transitions are the unique
factorizations between the original cocartesian lifts. Their universal property proves the
functor laws and strong cocartesianness, without a supplied section or coherence hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.GrothendieckCocartesian
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C) (x : F.obj ⟨R⟩)

/-- The actual factorization between the two original pullback images. -/
def sectionMap {i j : Under R} (a : i ⟶ j) : target x i.hom ⟶ target x j.hom := by
  have h : (Pseudofunctor.Grothendieck.forget F).IsHomLift
      (i.hom ≫ a.right) (lift x j.hom) := by
    rw [a.w]
    infer_instance
  exact factor x i.hom a.right (lift x j.hom)

instance instIsHomLiftSectionMap {i j : Under R} (a : i ⟶ j) :
    (Pseudofunctor.Grothendieck.forget F).IsHomLift a.right (sectionMap F R x a) :=
  IsHomLift.map _ (sectionMap F R x a)

/-- The section map retains the factorization through the actual initial lift. -/
theorem lift_sectionMap {i j : Under R} (a : i ⟶ j) :
    lift x i.hom ≫ sectionMap F R x a = lift x j.hom := by
  have h : (Pseudofunctor.Grothendieck.forget F).IsHomLift
      (i.hom ≫ a.right) (lift x j.hom) := by
    rw [a.w]
    infer_instance
  exact factor_fac x i.hom a.right (lift x j.hom)

/-- The actual section functor, with all functor laws proved by cocartesian uniqueness. -/
def sectionFunctor : Under R ⥤ Pseudofunctor.Grothendieck F where
  obj i := target x i.hom
  map a := sectionMap F R x a
  map_id i := by
    have hm : (Pseudofunctor.Grothendieck.forget F).IsHomLift
        (𝟙 i.right) (sectionMap F R x (𝟙 i)) := instIsHomLiftSectionMap F R x (𝟙 i)
    have hi : (Pseudofunctor.Grothendieck.forget F).IsHomLift
        (𝟙 i.right) (𝟙 (target x i.hom)) := IsHomLift.id rfl
    apply Functor.IsStronglyCocartesian.ext (Pseudofunctor.Grothendieck.forget F)
      i.hom (lift x i.hom) (𝟙 i.right)
    rw [lift_sectionMap, Category.comp_id]
  map_comp {i j k} a b := by
    have hm : (Pseudofunctor.Grothendieck.forget F).IsHomLift
        (a.right ≫ b.right) (sectionMap F R x (a ≫ b)) :=
      instIsHomLiftSectionMap F R x (a ≫ b)
    apply Functor.IsStronglyCocartesian.ext (Pseudofunctor.Grothendieck.forget F)
      i.hom (lift x i.hom) (a.right ≫ b.right)
    rw [lift_sectionMap, ← Category.assoc, lift_sectionMap, lift_sectionMap]

/-- The section lies literally over the original coslice forgetful functor. -/
theorem sectionFunctor_comp : sectionFunctor F R x ⋙ Pseudofunctor.Grothendieck.forget F =
    Under.forget R := rfl

/-- Every original object gives an actual strict section. -/
def strictSection : StrictSections (Pseudofunctor.Grothendieck.forget F) (Under.forget R) :=
  ⟨sectionFunctor F R x, sectionFunctor_comp F R x⟩

/-- Every transition of the original section is strongly cocartesian. -/
theorem section_cocartesian :
    StrictSections.cocartesian (Pseudofunctor.Grothendieck.forget F) (Under.forget R)
      (strictSection F R x) := by
  intro i j a
  have h : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (i.hom ≫ a.right) (lift x i.hom ≫ sectionMap F R x a) := by
    rw [lift_sectionMap, a.w]
    infer_instance
  exact Functor.IsStronglyCocartesian.of_comp (Pseudofunctor.Grothendieck.forget F)
    (f := i.hom) (g := a.right) (φ := lift x i.hom) (ψ := sectionMap F R x a)

/-- The original pullback section as an object of the actual cocartesian section category. -/
def cocartesianSection : StrictSections.underCocartesian
    (Pseudofunctor.Grothendieck.forget F) R :=
  ⟨strictSection F R x, section_cocartesian F R x⟩

end CategoryTheory.GrothendieckSections
