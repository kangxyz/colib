/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Length of a principal cut under a surjective ring map

The quotient by the kernel and the lifted equation retains its full module length.
No quotient is replaced by its reduction.
-/

@[expose] public noncomputable section

universe u v

namespace Module

/-- Surjective restriction retains the complete local quotient length. -/
theorem quotient_length_ker_sup_span
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (n : R) :
    Module.length R (R ⧸ (RingHom.ker φ ⊔ Ideal.span {n})) =
      Module.length S (S ⧸ Ideal.span {φ n}) := by
  let ψ := (Ideal.Quotient.mk (Ideal.span {φ n})).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hk : RingHom.ker ψ = RingHom.ker φ ⊔ Ideal.span {n} := by
    dsimp only [ψ]
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, sup_comm]
  let e : (R ⧸ (RingHom.ker φ ⊔ Ideal.span {n})) ≃+* (S ⧸ Ideal.span {φ n}) :=
    (Ideal.quotEquivOfEq hk.symm).trans (ψ.quotientKerEquivOfSurjective hψ)
  exact (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective
    (I := RingHom.ker φ ⊔ Ideal.span {n}))).trans
      ((Module.length_eq_of_ringEquiv e).trans
        (Module.length_eq_of_surjective
          (Ideal.Quotient.mk_surjective (I := Ideal.span {φ n}))).symm)

end Module
