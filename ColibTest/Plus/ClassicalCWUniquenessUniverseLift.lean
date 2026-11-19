module

public import Colib.Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift

set_option autoImplicit false

open Topology
open scoped Topology

universe u v w z

section CommonUniverse

variable {X₀ : Type u} {X₁ : Type v} {X₂ : Type w}
  [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
  [T2Space X₀] [T2Space X₁] [T2Space X₂]
  (A : Set X₀) (B : Set X₁) (C : Set X₂)
  [CWComplex A] [CWComplex B] [CWComplex C]

example
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    (hg : IsPlusConstruction.{u, w, max u v w z} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f).Homotopic g ∧
        ∀ k : C(B, C), (k.comp f).Homotopic g → k.Homotopic h.toFun :=
  IsPlusConstruction.classicalCWPlusUnique_commonUniverse A B C f g a b c γ δ N hf hg

end CommonUniverse

example
    {X₀ : Type u} {X₁ X₂ : Type (u + 1)}
    [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
    [T2Space X₀] [T2Space X₁] [T2Space X₂]
    (A : Set X₀) (B : Set X₁) (C : Set X₂)
    [CWComplex A] [CWComplex B] [CWComplex C]
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u + 1, u + 1} f γ N)
    (hg : IsPlusConstruction.{u, u + 1, u + 1} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f).Homotopic g ∧
        ∀ k : C(B, C), (k.comp f).Homotopic g → k.Homotopic h.toFun :=
  IsPlusConstruction.classicalCWPlusUnique_successor A B C f g a b c γ δ N hf hg

#print axioms Topology.IsPlusConstruction.exists_classicalCWComparison_commonUniverse
#print axioms Topology.IsPlusConstruction.classicalCWHomotopyCancelCommonUniverse
#print axioms Topology.IsPlusConstruction.classicalCWPlusUnique_commonUniverse
#print axioms Topology.IsPlusConstruction.classicalCWPlusUnique_successor
