/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Colib.RingTheory.Koszul.QuotientPair
public import Colib.RingTheory.Length.SurjectiveQuotient
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Principal intersection associativity for actual quotient Tor

The weights are the native localized lengths of the full quotient, not lengths
of its reduction. A scalar regular on the quotient is regular on every minimal
prime quotient, by the native associated-prime criterion. Its positive Tor on
those prime quotients vanishes by the native Koszul resolution. Consequently
the weighted alternating Tor sum equals the full double-cut length.

No flatness of the prime quotients over a geometric base is asserted. This is
a local algebraic producer; identifying these quotient Tor modules with graph
incidence stalk Tor and transporting finite-pushforward residue degrees are
separate geometric comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u

namespace Module

variable {R : Type u} [CommRing R]

/-- Regularity of the specialized equation makes the face equation regular on
the full original principal quotient. This uses no component flatness. -/
theorem isSMulRegular_quotient_span_swap (c n : R) (hc : IsSMulRegular R c)
    (hn : IsSMulRegular (R ⧸ Ideal.span {c}) n) :
    IsSMulRegular (R ⧸ Ideal.span {n}) c := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {n}) c).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  have hny : n • y ∈ Ideal.span {c} := by
    change n * y ∈ Ideal.span {c}
    rw [← hy]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton c))
  have hyc := (isSMulRegular_quotient_iff_mem_of_smul_mem
    (Ideal.span {c}) n).mp hn y hny
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hyc
  apply Ideal.mem_span_singleton.mpr
  refine ⟨z, ?_⟩
  apply hc
  change c * x = c * (n * z)
  change c * x = n * y at hy
  rw [hy, hz]
  ring

/-- The scalar cokernel of an ideal quotient retains the full double-cut length. -/
theorem length_scalarCokernel_quotient (c : R) (I : Ideal R) :
    Module.length R ((R ⧸ I) ⧸ LinearMap.range (LinearMap.lsmul R (R ⧸ I) c)) =
      Module.length R (R ⧸ (Ideal.span {c} ⊔ I)) := by
  rw [AlgebraicGeometry.range_lsmul_eq_smul_top]
  exact (AlgebraicGeometry.quotSMulTopQuotientEquiv c I).length_eq

/-- A regular principal quotient has no positive Tor against coefficients on
which its equation is regular. No flatness hypothesis on the coefficients occurs. -/
theorem isZero_tor_principal_of_regular [IsLocalRing R] (c : R)
    (hc : IsSMulRegular R c) (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M c)
    (i : ℕ) (hi : i ≠ 0) :
    IsZero (((Tor (ModuleCat R) i).obj
      (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj (ModuleCat.of R M)) := by
  have hs : RingTheory.Sequence.IsRegular R [c] :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (fun r hr => by simpa only [List.mem_singleton.mp hr] using hcm)).mpr
        ((RingTheory.Sequence.isWeaklyRegular_singleton_iff R c).mpr hc)
  let e := Koszul.torIsoHomologySeqComplexTensorOfIsRegular (fun _ : Fin 1 => c)
    (by simpa using hs) (Ideal.span {c}) (by simp) M i
  apply IsZero.of_iso _ e
  exact (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
    (by simpa using (RingTheory.Sequence.isWeaklyRegular_singleton_iff M c).mpr hM)) i hi

/-- The entire alternating Tor sum for a proper principal cut is its complete
quotient length. Every truncation including degree zero gives the same answer. -/
theorem sum_tor_principal_length_of_regular [IsLocalRing R] (c : R)
    (hc : IsSMulRegular R c) (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : IsSMulRegular (R ⧸ I) c) (b : ℕ) :
    (∑ i ∈ Finset.range (b + 1), (-1 : ℤ) ^ i *
      ((Module.length R (((Tor (ModuleCat R) i).obj
        (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj
          (ModuleCat.of R (R ⧸ I)))).toNat : ℤ)) =
      ((Module.length R (R ⧸ (Ideal.span {c} ⊔ I))).toNat : ℤ) := by
  rw [Finset.sum_eq_single 0]
  · simpa using congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (torZeroQuotientQuotientIso R (Ideal.span {c}) I).toLinearEquiv.length_eq
  · intro i _ hi
    have hz := isZero_tor_principal_of_regular c hc hcm (R ⧸ I) hI i hi
    have : Subsingleton (((Tor (ModuleCat R) i).obj
        (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj
          (ModuleCat.of R (R ⧸ I))) := ModuleCat.subsingleton_of_isZero hz
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · simp

/-- Weighted native quotient Tor equals the full local cut. Multiplicities are
actual localized lengths at the minimal support points of the unreduced quotient. -/
theorem quotient_tor_associativity [IsNoetherianRing R] [IsLocalRing R]
    (c : R) (hc : IsSMulRegular R c) (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (I : Ideal R) (hI : IsSMulRegular (R ⧸ I) c)
    (hfinite : Module.length R (R ⧸ (Ideal.span {c} ⊔ I)) ≠ ⊤) (b : ℕ) :
    (∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R (R ⧸ I)) q},
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (R ⧸ I))).toNat : ℤ) *
      (∑ i ∈ Finset.range (b + 1), (-1 : ℤ) ^ i *
        ((Module.length R (((Tor (ModuleCat R) i).obj
          (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj
            (ModuleCat.of R (R ⧸ q.asIdeal)))).toNat : ℤ))) =
      ((Module.length R (R ⧸ (Ideal.span {c} ⊔ I))).toNat : ℤ) := by
  have hcut : Module.length R ((R ⧸ I) ⧸
      LinearMap.range (LinearMap.lsmul R (R ⧸ I) c)) ≠ ⊤ := by
    rwa [length_scalarCokernel_quotient]
  rw [← length_scalarCokernel_quotient c I,
    principalCokernel_associativity c hcm hI hcut]
  apply finsum_mem_congr rfl
  intro q hq
  have hcq : c ∉ q.asIdeal :=
    hI.notMem_of_mem_minimalPrimes ((AlgebraicGeometry.minimal_support_iff q).mp hq)
  have hrq : IsSMulRegular (R ⧸ q.asIdeal) c := by
    intro x y hxy
    exact mul_left_cancel₀ (Ideal.Quotient.eq_zero_iff_mem.not.mpr hcq) hxy
  rw [sum_tor_principal_length_of_regular c hc hcm q.asIdeal hrq b,
    length_scalarCokernel_quotient]

/-- The actual surjective ring map identifies quotient Tor with Tor of its
literal target ring carrying the original restricted scalar action. -/
theorem length_tor_quotient_ker
    {S : Type u} [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ)
    (M : ModuleCat R) (i : ℕ) :
    Module.length R (((Tor (ModuleCat R) i).obj
      (ModuleCat.of R (R ⧸ RingHom.ker φ))).obj M) =
    Module.length R (((Tor (ModuleCat R) i).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj M) := by
  let := φ.toAlgebra
  let e : ModuleCat.of R (R ⧸ RingHom.ker φ) ≅
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId R S) hφ).toLinearEquiv.toModuleIso
  exact (((Tor (ModuleCat R) i).mapIso e).app M).toLinearEquiv.length_eq

/-- A nonzero image in a domain supplies regularity on the original kernel
quotient. Surjectivity and regularity of the source ring are unnecessary here. -/
theorem isSMulRegular_quotient_ker_of_domain_image
    {S : Type u} [CommRing S] [IsDomain S] (φ : R →+* S) (n : R)
    (hn : φ n ≠ 0) : IsSMulRegular (R ⧸ RingHom.ker φ) n := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (RingHom.ker φ) n).mpr
  intro x hx
  change φ (n * x) = 0 at hx
  change φ x = 0
  rw [map_mul] at hx
  exact (mul_eq_zero.mp hx).resolve_left hn

/-- A principal cut specialized through the actual surjective ring map computes
the weighted native Tor sum. Only a regular generator of that map's kernel is
required; regularity on each original principal component is proved above. -/
theorem principal_quotient_tor_associativity_of_surjective
    [IsNoetherianRing R] [IsLocalRing R]
    {S : Type u} [CommRing S] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (c n : R) (hc : IsSMulRegular R c)
    (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (hker : RingHom.ker φ = Ideal.span {c}) (hn : φ n ≠ 0)
    (hfinite : Module.length S (S ⧸ Ideal.span {φ n}) ≠ ⊤) (b : ℕ) :
    (∑ᶠ q ∈ {q : PrimeSpectrum R |
        Minimal (· ∈ Module.support R (R ⧸ Ideal.span {n})) q},
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (R ⧸ Ideal.span {n}))).toNat : ℤ) *
      (∑ i ∈ Finset.range (b + 1), (-1 : ℤ) ^ i *
        ((Module.length R (((Tor (ModuleCat R) i).obj
          (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj
            (ModuleCat.of R (R ⧸ q.asIdeal)))).toNat : ℤ))) =
      ((Module.length S (S ⧸ Ideal.span {φ n})).toNat : ℤ) := by
  have hspecial : IsSMulRegular (R ⧸ Ideal.span {c}) n := by
    rw [← hker]
    exact isSMulRegular_quotient_ker_of_domain_image φ n hn
  have hlen : Module.length R (R ⧸ (Ideal.span {c} ⊔ Ideal.span {n})) =
      Module.length S (S ⧸ Ideal.span {φ n}) := by
    rw [← hker]
    exact quotient_length_ker_sup_span φ hφ n
  rw [quotient_tor_associativity c hc hcm (Ideal.span {n})
    (isSMulRegular_quotient_span_swap c n hc hspecial)
    (hlen.symm ▸ hfinite) b, hlen]

end Module
