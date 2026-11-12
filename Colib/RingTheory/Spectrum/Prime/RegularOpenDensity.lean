/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Density of a principal regular open

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/Complement/CartierComplementDense.lean`,
blob `68a729ac9b8f42e11ce3acae493c8736aeea1ae8`.
Only the general ring-theoretic localization argument is extracted. No old
ideal-module or locally-rank-one API is imported.
-/
@[expose] public noncomputable section
universe u

namespace PrimeSpectrum

/-- Inverting a regular element gives a dense principal open, without a
Noetherian or reducedness assumption. -/
theorem dense_basicOpen_of_isRegular {R : Type u} [CommRing R]
    (a : R) (ha : IsRegular a) : Dense (basicOpen a : Set (PrimeSpectrum R)) := by
  have hinj : Function.Injective (algebraMap R (Localization.Away a)) := by
    apply IsLocalization.injectiveₛ (M := Submonoid.powers a)
    rintro _ ⟨n, rfl⟩
    exact IsRegular.pow n ha
  have hd : DenseRange (comap (algebraMap R (Localization.Away a))) := by
    apply (denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  change Dense (Set.range (comap (algebraMap R (Localization.Away a)))) at hd
  rwa [localization_away_comap_range (Localization.Away a) a] at hd

end PrimeSpectrum
