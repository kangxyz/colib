module

public import Colib.Topology.PlusConstruction.ClassicalCWUniqueness

set_option autoImplicit false

open CategoryTheory Topology
open scoped Topology

universe u

variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]
  [T2Space X₀] [T2Space X₁]
variable (A : Set X₀) (B : Set X₁) [CWComplex A] [CWComplex B]

example
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopy h₁ :=
  IsPlusConstruction.classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ H

variable {X₂ : Type u} [TopologicalSpace X₂] [T2Space X₂]
variable (C : Set X₂) [CWComplex C]

example
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f.hom).Homotopic g.hom ∧
        ∀ k : C(B, C), (k.comp f.hom).Homotopic g.hom → k.Homotopic h.toFun :=
  IsPlusConstruction.classicalCWPlusUnique A B C f g a b c γ δ N hf hg

#print axioms Topology.IsPlusConstruction.classicalCWHomotopyCancel
#print axioms Topology.IsPlusConstruction.classicalCWPlusUnique
