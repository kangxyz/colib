/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Exactness in a fixed singular degree

Each term of the original transfer singular complex is restriction along
the additive simplex exterior functor. The underlying restriction preserves
limits and colimits computed in abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Evaluation of the singular functor in a fixed simplex degree. -/
abbrev singularTermFunctor (n : ℕ) :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k :=
  singularComplexFunctor ⋙ HomologicalComplex.eval _ (.down ℕ) n

/-- The underlying functor is restriction along exterior product with the actual simplex. -/
theorem singularTermFunctor_comp_forget (n : ℕ) :
    singularTermFunctor n ⋙ AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{v} =
      restrictAlong (Cor.simplexExteriorFunctor n) := rfl

instance (n : ℕ) : PreservesFiniteLimits (singularTermFunctor n :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) := by
  let U := AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{v}
  let : U.Full := (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).fullyFaithfulι.full
  let : U.Faithful := (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).fullyFaithfulι.faithful
  let hU : ReflectsLimitsOfSize.{0, 0} U := fullyFaithful_reflectsLimits U
  let : ReflectsFiniteLimits U := { reflects J _ _ := hU.reflectsLimitsOfShape (J := J) }
  have h : singularTermFunctor n ⋙ U = restrictAlong (Cor.simplexExteriorFunctor n) :=
    singularTermFunctor_comp_forget n
  have : PreservesFiniteLimits (singularTermFunctor (k := k) n ⋙ U) := by
    rw [h]
    unfold restrictAlong
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

instance (n : ℕ) : PreservesFiniteColimits (singularTermFunctor n :
    PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) := by
  let U := AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{v}
  let : U.Full := (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).fullyFaithfulι.full
  let : U.Faithful := (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).fullyFaithfulι.faithful
  let hU : ReflectsColimitsOfSize.{0, 0} U := fullyFaithful_reflectsColimits U
  let : ReflectsFiniteColimits U := { reflects J _ _ := hU.reflectsColimitsOfShape (J := J) }
  have h : singularTermFunctor n ⋙ U = restrictAlong (Cor.simplexExteriorFunctor n) :=
    singularTermFunctor_comp_forget n
  have : PreservesFiniteColimits (singularTermFunctor (k := k) n ⋙ U) := by
    rw [h]
    unfold restrictAlong
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

end AlgebraicGeometry.PresheafWithTransfers
