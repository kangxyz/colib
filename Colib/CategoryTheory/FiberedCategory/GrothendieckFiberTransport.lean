/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiberComposition

/-!
# Original fiber components under endpoint transport

The actual base-equality transports in coefficient evaluation are carried through the original
fiber extraction; only the endpoints, rather than the geometric arrow, are transported.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace CategoryTheory.GrothendieckFiber
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- Source transport retains the actual extracted arrow and its original functor action. -/
@[colib_tag "COL-0356",
  colib_ref "quillen"
    "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckFiberTransport.lean"
    "adaptation" "Actual Grothendieck section transition and coefficient coherence"]
theorem liftedMap_precomp_eqToHom {R S : C} (f : R ⟶ S)
    {x x' : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (h : x = x') (φ : x'.val ⟶ y.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ] :
    liftedMap F f (eqToHom (congrArg Subtype.val h) ≫ φ) =
      (F.map f.toLoc).toFunctor.map (eqToHom (congrArg (originalObject F R) h)) ≫
        liftedMap F f φ := by
  subst x'
  simp only [eqToHom_refl, Category.id_comp, Functor.map_id]

/-- Target transport retains the actual extracted arrow. -/
theorem liftedMap_postcomp_eqToHom {R S : C} (f : R ⟶ S)
    {x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R}
    {y y' : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S}
    (h : y = y') (φ : x.val ⟶ y.val)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift f φ] :
    liftedMap F f (φ ≫ eqToHom (congrArg Subtype.val h)) =
      liftedMap F f φ ≫ eqToHom (congrArg (originalObject F S) h) := by
  subst y'
  simp only [eqToHom_refl, Category.comp_id]

end CategoryTheory.GrothendieckFiber
