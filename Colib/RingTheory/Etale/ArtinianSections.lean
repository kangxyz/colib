/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Prescribed residue sections over an Artinian local ring

The maximal ideal is nilpotent, so the native formal-smooth lifting theorem
lifts the actual residue algebra map. This supplies the Artinian specialization
of `Motivic/Aglib/RingTheory/Etale/HenselianSections.lean`, blob
`e2062e093efac29d43617224e5260356ca6dd3fe`, at
`kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
No duplicate henselian lifting development or reducedness assumption is needed.
-/

@[expose] public section

namespace Algebra.Etale.Artinian

open IsLocalRing

/-- The prescribed reduction lifts over the full, possibly nonreduced local ring. -/
theorem exists_lift_of_etale {R B : Type*} [CommRing R] [CommRing B]
    [IsLocalRing R] [IsArtinianRing R] [Algebra R B] [Algebra.Etale R B]
    (φ : B →ₐ[R] ResidueField R) :
    ∃ ψ : B →ₐ[R] R, (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ := by
  have hm : IsNilpotent (maximalIdeal R) := by
    rw [← jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  exact Algebra.FormallySmooth.exists_lift (maximalIdeal R) hm φ

end Algebra.Etale.Artinian
