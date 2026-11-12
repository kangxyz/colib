/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.QuotientTor

/-!
# Native Tor of the actual quotient-target modules

Two actual surjective ring maps supply their own kernel-quotient module
isomorphisms. When the first kernel is a regular principal equation and that
equation remains nonzero in the integral second target, the full native Tor
Euler coefficient is the full principal quotient length in the second target.
Neither target module is replaced by its reduced support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Module

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The original actions of both actual surjective target modules agree with
their literal native kernel quotients in every Tor degree. -/
theorem length_tor_two_surjective_targets
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (ψ : R →+* T) (hψ : Function.Surjective ψ) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj
      (ModuleCat.of R (R ⧸ RingHom.ker φ))).obj
        (ModuleCat.of R (R ⧸ RingHom.ker ψ))) =
      Module.length R (((Tor (ModuleCat R) n).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
          ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T))) := by
  rw [length_tor_quotient_ker φ hφ]
  let := ψ.toAlgebra
  let e : ModuleCat.of R (R ⧸ RingHom.ker ψ) ≅
      (ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId R T) hψ).toLinearEquiv.toModuleIso
  exact (((Tor (ModuleCat R) n).obj
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).mapIso e).toLinearEquiv.length_eq

/-- Degree zero already identifies the full extended length, before taking
any natural-number coefficient. No regularity or finite-length premise is needed. -/
theorem length_torZero_surjective_principal_cut
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (ψ : R →+* T) (hψ : Function.Surjective ψ)
    (c : R) (hker : RingHom.ker φ = Ideal.span {c}) :
    Module.length R (((Tor (ModuleCat R) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
        ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T))) =
      Module.length T (T ⧸ Ideal.span {ψ c}) := by
  rw [← length_tor_two_surjective_targets φ hφ ψ hψ, hker]
  rw [(torZeroQuotientQuotientIso R (Ideal.span {c}) (RingHom.ker ψ)).toLinearEquiv.length_eq]
  rw [sup_comm, quotient_length_ker_sup_span ψ hψ]

/-- Actual surjective target modules have the complete principal cut as their
native Tor Euler coefficient. Every truncation containing degree zero agrees. -/
theorem sum_tor_surjective_principal_cut [IsLocalRing R] [IsDomain T]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (ψ : R →+* T) (hψ : Function.Surjective ψ)
    (c : R) (hc : IsSMulRegular R c) (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (hker : RingHom.ker φ = Ideal.span {c}) (hψc : ψ c ≠ 0) (b : ℕ) :
    (∑ n ∈ Finset.range (b + 1), (-1 : ℤ) ^ n *
      ((Module.length R (((Tor (ModuleCat R) n).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
          ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T)))).toNat : ℤ)) =
      ((Module.length T (T ⧸ Ideal.span {ψ c})).toNat : ℤ) := by
  have hq : IsSMulRegular (R ⧸ RingHom.ker ψ) c :=
    isSMulRegular_quotient_ker_of_domain_image ψ c hψc
  calc
    _ = ∑ n ∈ Finset.range (b + 1), (-1 : ℤ) ^ n *
        ((Module.length R (((Tor (ModuleCat R) n).obj
          (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj
            (ModuleCat.of R (R ⧸ RingHom.ker ψ)))).toNat : ℤ) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [← length_tor_two_surjective_targets φ hφ ψ hψ, hker]
    _ = ((Module.length R (R ⧸ (Ideal.span {c} ⊔ RingHom.ker ψ))).toNat : ℤ) :=
      sum_tor_principal_length_of_regular c hc hcm (RingHom.ker ψ) hq b
    _ = _ := by rw [sup_comm, quotient_length_ker_sup_span ψ hψ]

end Module
