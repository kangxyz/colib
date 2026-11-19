/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.PlusConstruction.ClassicalCWComparison

/-!
# Ordinary uniqueness of plus constructions on classical CW complexes

For two plus constructions of the same kernel, the mixed double cylinder
provides a comparison equivalence. The self cylinder gives cancellation of
precomposition with the first plus map, into any same-universe space. This is
ordinary homotopy uniqueness, with no coherence of the homotopies under the
source asserted.

Adapted from `Quillen/Topology/PlusConstruction/ClassicalCWUniqueness.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology
open scoped Topology unitInterval

universe u

namespace Topology.IsPlusConstruction

open TopCat.DoubleCylinder

variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]
  [T2Space X₀] [T2Space X₁]
variable (A : Set X₀) (B : Set X₁) [CWComplex A] [CWComplex B]

/-- Precomposition by the given plus map cancels on homotopies into any
same-universe space. The self cylinder uses its canonical pushout and cover. -/
def classicalCWHomotopyCancel
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopy h₁ := by
  let D : TopCat.{u} := pushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f f)
  let l : TopCat.of A ⊗ TopCat.I ⟶ D := pushout.inl _ _
  let e : TopCat.of (B ⊕ B) ⟶ D := pushout.inr _ _
  have sq : IsPushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f f) l e :=
    IsPushout.of_hasPushout _ _
  have hL := (plus_legs_isWeakHomotopyEquivalence_of_cw A B B f f sq a b b γ γ N hf hf).1
  let L := cwLeftEndpointHomotopyEquiv A B B f f sq hL
  exact homotopyCancelOfLeftLegEquiv f sq L rfl h₀ h₁ H

include A B in
/-- Maps supplied with homotopies under the original source are ordinarily
homotopic. The original under-source homotopies are not compared. -/
theorem homotopic_classicalCWComparisons
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (k : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopic k) (H₁ : (h₁.comp f.hom).Homotopic k) :
    h₀.Homotopic h₁ :=
  ⟨classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ (H₀.some.trans H₁.some.symm)⟩

variable {X₂ : Type u} [TopologicalSpace X₂] [T2Space X₂]
variable (C : Set X₂) [CWComplex C]

include A B C in
/-- Two plus constructions on classical CW subtypes with the same kernel admit
a homotopy equivalence under the source, unique up to ordinary homotopy among
all continuous maps compatible with the source up to homotopy. -/
theorem classicalCWPlusUnique
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f.hom).Homotopic g.hom ∧
        ∀ k : C(B, C), (k.comp f.hom).Homotopic g.hom → k.Homotopic h.toFun := by
  obtain ⟨h, H⟩ := exists_classicalCWComparison A B C f g a b c γ δ N hf hg
  exact ⟨h, H, fun k Hk ↦
    homotopic_classicalCWComparisons A B f a b γ N hf g.hom k h.toFun Hk H⟩

attribute [colib_tag "COL-1311"] classicalCWPlusUnique

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/ClassicalCWUniqueness.lean:124-137"
  "adaptation" "Comparison and ordinary uniqueness for the original same-universe CW plus maps"]
  classicalCWPlusUnique

end Topology.IsPlusConstruction
