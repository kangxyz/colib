/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Inversion detected by a natural comparison of represented Hom functors

This is the categorical argument used by Nisnevich parameter-tensor descent:
a natural comparison of Hom functors transfers invertibility from one functor
to another. It does not depend on a topology, a reflection, or a derived model.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {L : C ⥤ D} {T : C ⥤ E}

/-- A natural comparison of represented Hom functors makes `T` invert every
morphism inverted by `L`. Only an object assignment on the test objects is needed. -/
theorem isIso_map_of_naturalHomEquiv (S : E → D)
    (e : ∀ (X : C) (Y : E), (T.obj X ⟶ Y) ≃ (L.obj X ⟶ S Y))
    (he : ∀ {X X' : C} (f : X ⟶ X') (Y : E) (g : T.obj X' ⟶ Y),
      e X Y (T.map f ≫ g) = L.map f ≫ e X' Y g)
    {X X' : C} (f : X ⟶ X') [IsIso (L.map f)] : IsIso (T.map f) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  let h := (asIso (L.map f)).symm
  have hcomp : e X Y ∘ (fun g : T.obj X' ⟶ Y => T.map f ≫ g) =
      h.homFromEquiv ∘ e X' Y := by
    funext g
    exact he f Y g
  apply (Function.Bijective.of_comp_iff' (e X Y).bijective _).1
  rw [hcomp]
  exact h.homFromEquiv.bijective.comp (e X' Y).bijective

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {T : C ⥤ E} {S : E ⥤ D} (adjT : T ⊣ S ⋙ R)

include adj adjT in
/-- A right adjoint factoring through another right adjoint makes its left
adjoint invert every map inverted by the other left adjoint. -/
theorem isIso_map_of_isIso_leftAdjoint_map {X Y : C} (f : X ⟶ Y)
    [IsIso (L.map f)] : IsIso (T.map f) := by
  apply Functor.isIso_map_of_naturalHomEquiv S.obj
    (fun X Y => (adjT.homEquiv X Y).trans (adj.homEquiv X (S.obj Y)).symm) _ f
  intro X X' g Y q
  dsimp only [Equiv.trans_apply]
  rw [adjT.homEquiv_naturality_left, adj.homEquiv_naturality_left_symm]

end CategoryTheory.Adjunction
