/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.GenericEuler
public import StacksFrontier.RingTheory.Length.FibreLengthSum
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Data.ENat.BigOperators

/-!
# Original generic residue degrees in finite-pushforward Euler devissage

For a finite algebra over a Noetherian local image ring, native generic Euler
is applied to the actual restricted coefficient module. Each generic image
weight is then expanded by the native finite-fibre length theorem over every
original prime above that image label. These are minimal source primes by
native quasi-finite incomparability. Distinct original labels are never merged.

The support condition in native `length_localizedModule_eq_finsum_fibre` is
proved from minimality of the image prime, not supplied by a caller. Finite
fibres and finite total length justify conversion from extended-natural to
integer lengths. Every minimal image label remains, including the lower-
dimensional ones whose Euler contribution vanishes in `GenericEuler`.

The residue degrees here are the original generic degrees, not the degrees of
a later closed remaining-intersection fibre. The signed-family endpoint applies
the formula degreewise to the actual first homology modules. Finite maps need
not be flat, reduced, local, or injective.

Native inputs: Stacks 02M0 via `Length.FibreLengthSum`, and 0AZX/0AZZ via
`Koszul.GenericEuler`. The finite-fibre and prime-filtration proofs are reused,
not reconstructed. Geometric label/glueing identification remains separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace Koszul

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Every prime over a minimal image prime is an original minimal source prime.
This is native quasi-finite incomparability; no dominance premise is added. -/
theorem isMin_of_isMin_comap_finiteAlgebra (q : PrimeSpectrum S)
    (hq : IsMin (PrimeSpectrum.comap (algebraMap R S) q)) : IsMin q := by
  intro q' hle
  have he : PrimeSpectrum.comap (algebraMap R S) q' =
      PrimeSpectrum.comap (algebraMap R S) q :=
    le_antisymm (Ideal.comap_mono hle) (hq (Ideal.comap_mono hle))
  have hqeq := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) q'.asIdeal q.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal he)
  exact (PrimeSpectrum.ext hqeq).ge

/-- Integer generic length of the actual restricted module, expanded over
all original labels above the image generic point with their genuine residue degrees. -/
theorem lengthToNat_localized_restrictScalars_eq_finsum_fibre [IsNoetherianRing R]
    (p : PrimeSpectrum R) (hp : IsMin p) (M : ModuleCat.{u} S) [Module.Finite S M] :
    ((Module.length (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl
        ((ModuleCat.restrictScalars (algebraMap R S)).obj M))).toNat : ℤ) =
      ∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.asIdeal},
        (Stacks.Length.primeResidueDegree (algebraMap R S) p.asIdeal q.asIdeal : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) := by
  classical
  let : Module R M := ((ModuleCat.restrictScalars (algebraMap R S)).obj M).isModule
  let : IsScalarTower R S M := .of_algebraMap_smul fun _ _ => rfl
  have hsupp : ∀ q : PrimeSpectrum S, q ∈ Module.support S M →
      q.asIdeal.comap (algebraMap R S) ≤ p.asIdeal →
        q.asIdeal.comap (algebraMap R S) = p.asIdeal := by
    intro q _ hle
    exact congrArg PrimeSpectrum.asIdeal
      (show PrimeSpectrum.comap (algebraMap R S) q = p from le_antisymm hle (hp hle))
  let F := {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.asIdeal}
  have hF : F.Finite :=
    (Algebra.QuasiFinite.finite_comap_preimage_singleton (R := R) (S := S) p).subset
      (fun q hq => PrimeSpectrum.ext hq)
  have h := Stacks.Length.length_localizedModule_eq_finsum_fibre p.asIdeal M hsupp
  have hne := Stacks.Length.length_localizedModule_ne_top_of_fibre p.asIdeal M hsupp
  rw [finsum_mem_eq_finite_toFinset_sum _ hF] at h
  have hsumne : (∑ q ∈ hF.toFinset,
      (Stacks.Length.primeResidueDegree (algebraMap R S) p.asIdeal q.asIdeal : ℕ∞) *
        Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)) ≠ ⊤ := by
    rwa [← h]
  have hnat := congrArg ENat.toNat h
  rw [ENat.toNat_sum (WithTop.sum_ne_top.mp hsumne)] at hnat
  change ((Module.length (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl M)).toNat : ℤ) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, hnat, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul]

/-- Generic Euler devissage of the finite direct image, with each coefficient
expanded into the original generic source length and original residue degree. -/
theorem seqEuler_restrictScalars_eq_finsum_generic_fibres
    [IsNoetherianRing R] [IsLocalRing R] {r : ℕ}
    (f : Fin r → R) (M : ModuleCat.{u} S) [Module.Finite S M]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) :
    seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.1.asIdeal},
          (Stacks.Length.primeResidueDegree (algebraMap R S) p.1.asIdeal q.asIdeal : ℤ) *
            ((Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ)) *
                seqEuler f (R ⧸ p.1.asIdeal) := by
  let : Module R M := ((ModuleCat.restrictScalars (algebraMap R S)).obj M).isModule
  let : IsScalarTower R S M := .of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
    show Module.Finite R M from Module.Finite.trans S M
  rw [seqEuler_eq_finsum_minimalPrimes f
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M) hI]
  apply finsum_congr
  intro p
  rw [lengthToNat_localized_restrictScalars_eq_finsum_fibre p.1 p.2 M]

/-- The original higher-homology signs are retained inside each generic-image
coefficient, whose fibre sum retains every colliding original label separately. -/
theorem sum_signed_seqEuler_restrictScalars_eq_finsum_generic_fibres
    [IsNoetherianRing R] [IsLocalRing R] {r : ℕ}
    (f : Fin r → R) (M : ℕ → ModuleCat.{u} S) [∀ b, Module.Finite S (M b)]
    (hI : IsIdealOfDefinition (Ideal.span (Set.range f))) (J : Finset ℕ) :
    ∑ b ∈ J, (-1 : ℤ) ^ b *
      seqEuler f ((ModuleCat.restrictScalars (algebraMap R S)).obj (M b)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p.1.asIdeal},
            (Stacks.Length.primeResidueDegree (algebraMap R S) p.1.asIdeal q.asIdeal : ℤ) *
              ((Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl (M b))).toNat : ℤ)) *
                  seqEuler f (R ⧸ p.1.asIdeal) := by
  let N := fun b => (ModuleCat.restrictScalars (algebraMap R S)).obj (M b)
  let : ∀ b, Module R (M b) := fun b => (N b).isModule
  let : ∀ b, IsScalarTower R S (M b) := fun b => .of_algebraMap_smul fun _ _ => rfl
  let : ∀ b, Module.Finite R (N b) := fun b =>
    show Module.Finite R (M b) from Module.Finite.trans S (M b)
  have he := sum_signed_seqEuler_eq_finsum_minimalPrimes f (fun b => (N b : Type u)) hI J
  rw [he]
  apply finsum_congr
  intro p
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [lengthToNat_localized_restrictScalars_eq_finsum_fibre p.1 p.2 (M b)]

end Koszul
