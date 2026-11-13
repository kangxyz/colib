/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.NormalComponents
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Integrality from one entire singleton fiber

For a finite open morphism with normal locally Noetherian source and connected
target, every irreducible component maps onto the target. A nonempty singleton
fiber meets every component and forces the whole source to be irreducible.

This reconstructs the finite-etale singleton-fiber argument of motivic
`a6805c4a87cdfd7717dd7a94039246a167f15380` using native normal components.
Neither a selected component nor a selected point in a larger fiber suffices.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A finite open morphism with one nonempty singleton entire fiber has integral
source when the source is normal and locally Noetherian and the target is connected. -/
theorem isIntegral_of_finite_open_singletonFiber_of_isNormal
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [PreconnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [UniversallyOpen f]
    (x₀ : X) (hf : ∀ x : X, f x = f x₀ → x = x₀) : IsIntegral X := by
  have hsurj (W : Set X) (hW : W ∈ irreducibleComponents X) :
      f '' W = Set.univ := by
    have hcl := isClopen_of_mem_irreducibleComponents_of_isNormal W hW
    have him : IsClopen (f '' W) := ⟨f.isClosedMap W hcl.1, f.isOpenMap W hcl.2⟩
    exact him.eq_univ (hW.1.1.image f)
  have hcomp : irreducibleComponent x₀ = (Set.univ : Set X) := by
    apply Set.eq_univ_of_forall
    intro x
    let W := irreducibleComponent x
    have hW : W ∈ irreducibleComponents X :=
      irreducibleComponent_mem_irreducibleComponents x
    have hx₀ : f x₀ ∈ f '' W := by rw [hsurj W hW]; trivial
    obtain ⟨x', hx', heq⟩ := hx₀
    have hx₀W : x₀ ∈ W := hf x' heq ▸ hx'
    have he : W = irreducibleComponent x₀ := by
      by_contra hne
      exact Set.disjoint_left.mp
        (disjoint_of_mem_irreducibleComponents_of_isNormal W (irreducibleComponent x₀)
          hW (irreducibleComponent_mem_irreducibleComponents x₀) hne)
        hx₀W mem_irreducibleComponent
    exact he ▸ (mem_irreducibleComponent : x ∈ irreducibleComponent x)
  have hirr : IsIrreducible (irreducibleComponent x₀) :=
    isIrreducible_irreducibleComponent
  rw [hcomp] at hirr
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- A finite étale morphism is open, so one entire singleton fiber suffices. -/
theorem isIntegral_of_finite_etale_singletonFiber_of_isNormal
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [PreconnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (x₀ : X) (hf : ∀ x : X, f x = f x₀ → x = x₀) : IsIntegral X :=
  isIntegral_of_finite_open_singletonFiber_of_isNormal f x₀ hf

end AlgebraicGeometry.Scheme
