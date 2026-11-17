/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Monoidal.TensorPow
public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct

/-!
# Products and exact right actions of native tensor powers

The product is built from the original right unitor and associator, with no replacement
of the native left-associated tensor powers.
-/

@[expose] public noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Concatenation of two native left-associated tensor powers. -/
def tensorPowAddHom (X : C) (p : ℕ) : (q : ℕ) →
    tensorPow X p ⊗ tensorPow X q ⟶ tensorPow X (p + q)
  | 0 => (ρ_ (tensorPow X p)).hom
  | q + 1 => (α_ (tensorPow X p) (tensorPow X q) X).inv ≫
      tensorPowAddHom X p q ▷ X

/-- The empty right factor is removed by the original right unitor. -/
@[simp] theorem tensorPowAddHom_zero (X : C) (p : ℕ) :
    tensorPowAddHom X p 0 = (ρ_ (tensorPow X p)).hom := rfl

/-- Concatenation appends the last factor through the original associator. -/
@[simp] theorem tensorPowAddHom_succ (X : C) (p q : ℕ) :
    tensorPowAddHom X p (q + 1) =
      (α_ (tensorPow X p) (tensorPow X q) X).inv ≫
        tensorPowAddHom X p q ▷ X := rfl

variable [Abelian C]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exactness of tensoring on the right propagates to every native tensor power. -/
theorem exact_tensorRight_tensorPow (X : C) [(tensorRight X).Additive]
    [PreservesFiniteLimits (tensorRight X)] [PreservesFiniteColimits (tensorRight X)]
    (q : ℕ) : (tensorRight (tensorPow X q)).Additive ∧
      PreservesFiniteLimits (tensorRight (tensorPow X q)) ∧
      PreservesFiniteColimits (tensorRight (tensorPow X q)) := by
  induction q with
  | zero =>
    simp only [tensorPow_zero]
    let := Functor.additive_of_iso (rightUnitorNatIso C).symm
    let := preservesFiniteLimits_of_natIso (rightUnitorNatIso C).symm
    let := preservesFiniteColimits_of_natIso (rightUnitorNatIso C).symm
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | succ q ih =>
    simp only [tensorPow_succ]
    let := ih.1
    let := ih.2.1
    let := ih.2.2
    let := Functor.additive_of_iso (tensorRightTensor (tensorPow X q) X).symm
    let := preservesFiniteLimits_of_natIso (tensorRightTensor (tensorPow X q) X).symm
    let := preservesFiniteColimits_of_natIso (tensorRightTensor (tensorPow X q) X).symm
    exact ⟨inferInstance, inferInstance, inferInstance⟩
end CategoryTheory.MonoidalCategory
