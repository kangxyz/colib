/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.PlusConstruction.ClassicalCWComparison

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Topology TopCat.DoubleCylinder
open scoped unitInterval

universe u

section

variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
example (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C, (h.toFun.comp f.hom).Homotopic g.hom :=
  IsPlusConstruction.exists_classicalCWComparison A B C f g a b c γ δ N hf hg

end

#print axioms TopCat.DoubleCylinder.plus_legs_isWeakHomotopyEquivalence_of_cw
#print axioms Topology.IsPlusConstruction.exists_classicalCWComparison
