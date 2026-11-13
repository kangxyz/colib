/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import StacksFrontier.Algebra.Homology.TotalComplexShortExact
import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit

/-!
# Exactness of totalization with exact antidiagonal coproducts

Evaluation in a total degree sends a degreewise short exact sequence
to the coproduct of its short exact sequences on that antidiagonal.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex₂

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "c" => ComplexShape.up ℤ

variable (S : ShortComplex (HomologicalComplex₂ A c c))
  [S.X₁.HasTotal c] [S.X₂.HasTotal c] [S.X₃.HasTotal c]

/-- A bidegreewise short exact sequence remains short exact on
totalization when the antidiagonal coproducts are exact. -/
theorem shortExact_total_of_bidegreewise
    [∀ n : ℤ, HasColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) A]
    [∀ n : ℤ, HasExactColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) A]
    (hS : ∀ p q : ℤ,
      (S.map (HomologicalComplex.eval _ c p ⋙ HomologicalComplex.eval A c q)).ShortExact) :
    (ShortComplex.mk (total.map S.f c) (total.map S.g c)
      (by rw [← total.map_comp, S.zero, total_map_zero])).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let I := ↥(ComplexShape.π c c c ⁻¹' {n})
  let D (K : HomologicalComplex₂ A c c) : Discrete I ⥤ A :=
    Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c c c) n)
  let f : D S.X₁ ⟶ D S.X₂ := Discrete.natTrans (fun i => (S.f.f i.as.val.1).f i.as.val.2)
  let g : D S.X₂ ⟶ D S.X₃ := Discrete.natTrans (fun i => (S.g.f i.as.val.1).f i.as.val.2)
  have hz : f ≫ g = 0 := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun m : S.X₁ ⟶ S.X₃ => (m.f i.as.val.1).f i.as.val.2) S.zero
  let T := ShortComplex.mk f g hz
  have hT : T.ShortExact := ShortComplex.shortExact_of_app _ (fun i => hS i.as.val.1 i.as.val.2)
  let F : (Discrete I ⥤ A) ⥤ A := colim
  let : PreservesFiniteLimits F := HasExactColimitsOfShape.preservesFiniteLimits
  have h := hT.map_of_exact F
  exact h

end HomologicalComplex₂
