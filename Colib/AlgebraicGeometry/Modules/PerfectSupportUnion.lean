/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportRestrictionVanishing

/-! # Actual acyclicity on a union of opens

The native stalkwise homology criterion proves the union formula directly, for
arbitrary schemes and opens. The supported predicate is unchanged and no derived
replacement is introduced. Adapted from Quillen/Aglib/AlgebraicGeometry/Modules/
PerfectComplexes/Support/Union.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Vanishing on an open union is equivalent to vanishing on both actual opens. -/
theorem restrictAcyclic_sup_iff {X : Scheme.{u}} (U T : X.Opens)
    (K : CochainComplex X.Modules ℤ) :
    (((restrictFunctor (U ⊔ T).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ↔
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ∧
        (((restrictFunctor T.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  simp only [restrictAcyclic_iff_stalkHomology]
  constructor
  · intro h
    exact ⟨fun n x => h n ⟨x.val, Or.inl x.property⟩,
      fun n x => h n ⟨x.val, Or.inr x.property⟩⟩
  · rintro ⟨hU, hT⟩ n x
    rcases x.property with hx | hx
    · exact hU n ⟨x.val, hx⟩
    · exact hT n ⟨x.val, hx⟩

/-- Vanishing on the image open is exactly vanishing under the original immersion. -/
theorem restrictAcyclic_opensRange_iff {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) :
    (((restrictFunctor j.opensRange.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ↔
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  simp only [restrictAcyclic_iff_stalkHomology]
  constructor
  · intro h n x
    exact h n ⟨j x, ⟨x, rfl⟩⟩
  · intro h n x
    obtain ⟨y, hy⟩ := x.property
    simpa only [Scheme.Opens.ι_apply, hy] using h n y

/-- The original support on the complement of a union is the intersection of the two
actual acyclicity conditions, with native perfectness retained. -/
theorem perfectSupported_sup_opensRange_iff {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (T : X.Opens) (K : CochainComplex X.Modules ℤ) :
    perfectSupported (T ⊔ j.opensRange).ι K ↔ perfectSupported T.ι K ∧
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  simp only [perfectSupported, restrictAcyclic_sup_iff, restrictAcyclic_opensRange_iff]
  exact and_assoc.symm

end AlgebraicGeometry.Scheme.Modules
