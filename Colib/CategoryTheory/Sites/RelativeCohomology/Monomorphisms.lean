/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.RelativeCohomology.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Monomorphisms of native free representing sheaves

Hom-injectivity, the native free abelian group functor, and left exact
sheafification preserve the original monomorphism of site objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- The native free representing sheaf carries a site monomorphism to a monomorphism. -/
theorem freeYoneda_map_mono {U X : C} (j : U ⟶ X) [Mono j] :
    Mono ((freeYoneda.{t} J).map j) := by
  have hmono : Mono (uliftYoneda.{t}.map j) := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro Z
    apply ConcreteCategory.mono_of_injective
    intro x y h
    apply ULift.ext
    apply (cancel_mono j).mp
    exact congrArg ULift.down h
  change Mono ((presheafToSheaf J AddCommGrpCat.{max v t}).map
    (((Functor.whiskeringRight Cᵒᵖ (Type max v t) AddCommGrpCat.{max v t}).obj
      AddCommGrpCat.free).map (uliftYoneda.{t}.map j)))
  infer_instance

end Stacks.Cohomology.FreeYonedaUnivLE
