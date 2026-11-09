/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiberMap

/-!
# Original fiber components of composite lifted arrows

The equations retain the actual pseudofunctor unit and composition comparisons, including the
canonical transports from the given strict fibers.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace CategoryTheory.GrothendieckFiber
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- Equality of actual lifted arrows preserves their original fiber components. -/
theorem liftedMap_congr {R S : C} (f : R ⟶ S)
    {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (φ ψ : x.val ⟶ y.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ]
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f ψ] (h : φ = ψ) :
    liftedMap F f φ = liftedMap F f ψ := by
  subst ψ
  rfl

/-- Fiber extraction preserves composition with the actual pseudofunctor comparison. -/
@[colib_tag "COL-0356",
  colib_ref "quillen"
    "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckFiberComposition.lean"
    "adaptation" "Actual Grothendieck section transition and coefficient coherence"]
theorem liftedMap_comp {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    {z : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) T}
    (φ : x.val ⟶ y.val) (ψ : y.val ⟶ z.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ]
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift g ψ] :
    liftedMap F (f ≫ g) (φ ≫ ψ) =
      (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app (originalObject F R x) ≫
        (F.map g.toLoc).toFunctor.map (liftedMap F f φ) ≫ liftedMap F g ψ := by
  rcases x with ⟨⟨R', x⟩, hx⟩
  rcases y with ⟨⟨S', y⟩, hy⟩
  rcases z with ⟨⟨T', z⟩, hz⟩
  change R' = R at hx
  change S' = S at hy
  change T' = T at hz
  subst R'
  subst S'
  subst T'
  have hf : φ.base = f := by
    have h := IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) f φ
    change φ.base = eqToHom (show R = R from rfl) ≫ f ≫
      eqToHom (show S = S from rfl) at h
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  have hg : ψ.base = g := by
    have h := IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) g ψ
    change ψ.base = eqToHom (show S = S from rfl) ≫ g ≫
      eqToHom (show T = T from rfl) at h
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  subst f
  subst g
  change (𝟙 ((F.map (φ.base ≫ ψ.base).toLoc).toFunctor.obj x)) ≫
      ((F.mapComp φ.base.toLoc ψ.base.toLoc).hom.toNatTrans.app x ≫
        (F.map ψ.base.toLoc).toFunctor.map φ.fiber ≫ ψ.fiber) =
    (F.mapComp φ.base.toLoc ψ.base.toLoc).hom.toNatTrans.app x ≫
      (F.map ψ.base.toLoc).toFunctor.map
        ((𝟙 ((F.map φ.base.toLoc).toFunctor.obj x)) ≫ φ.fiber) ≫
      (𝟙 ((F.map ψ.base.toLoc).toFunctor.obj y)) ≫ ψ.fiber
  simp only [Category.id_comp]
  rfl

/-- Fiber extraction of the identity retains the actual pseudofunctor unit. -/
theorem liftedMap_id {R : C}
    (x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R) :
    letI := IsHomLift.id x.property
    liftedMap F (𝟙 R) (𝟙 x.val) =
      (F.mapId ⟨R⟩).hom.toNatTrans.app (originalObject F R x) := by
  rcases x with ⟨⟨R', x⟩, hx⟩
  change R' = R at hx
  subst R'
  have : (Pseudofunctor.Grothendieck.forget F).IsHomLift (𝟙 R)
      (𝟙 (⟨R, x⟩ : Pseudofunctor.Grothendieck F)) := IsHomLift.id rfl
  change (𝟙 ((F.map (𝟙 R).toLoc).toFunctor.obj x)) ≫
      (F.mapId ⟨R⟩).hom.toNatTrans.app x = (F.mapId ⟨R⟩).hom.toNatTrans.app x
  exact Category.id_comp _

end CategoryTheory.GrothendieckFiber
