/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport

/-! # Comparison with a tensor transported along an equivalence -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal

/-- The tensor transported by an equivalence agrees with a bifunctor that uses the same
objects and the same two whiskerings at the chosen representatives. -/
def transportTensorIso {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    (e : C ≌ D) (T : D ⥤ D ⥤ D)
    (i : ∀ X Y : D, e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y) ≅ (T.obj X).obj Y)
    (h₁ : ∀ {X X' : D} (f : X ⟶ X') (Y : D),
      e.functor.map (e.inverse.map f ▷ e.inverse.obj Y) ≫ (i X' Y).hom =
        (i X Y).hom ≫ (T.map f).app Y)
    (h₂ : ∀ (X : D) {Y Y' : D} (g : Y ⟶ Y'),
      e.functor.map (e.inverse.obj X ◁ e.inverse.map g) ≫ (i X Y').hom =
        (i X Y).hom ≫ (T.obj X).map g) :
    letI := transport e
    curriedTensor D ≅ T := by
  let := transport e
  refine NatIso.ofComponents (fun X => NatIso.ofComponents (i X) (fun g => h₂ X g))
    (fun f => ?_)
  exact NatTrans.ext (funext (h₁ f))

end CategoryTheory.Monoidal
