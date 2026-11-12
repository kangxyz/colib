/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Height
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic.Localization
public import StacksFrontier.RingTheory.Length.FibreLengthSum
public import StacksFrontier.RingTheory.Norm.Projective
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm

/-!
# Length of the principal quotient of a finite free algebra

Over a one-dimensional local domain, the determinant of multiplication
computes the full length of the original quotient. The algebra may have
several components and the element is a nonzerodivisor on the entire algebra.
-/

@[expose] public noncomputable section

universe u v

namespace LinearMap

/-- The determinant length of a finite free endomorphism computes the
length of its original cokernel. -/
theorem length_quotient_range_eq_length_quotient_det
    {A : Type u} {M : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] (φ : M →ₗ[A] M) (hdet : φ.det ≠ 0) :
    Module.length A (M ⧸ φ.range) = Module.length A (A ⧸ Ideal.span {φ.det}) := by
  let b := Module.finBasis A M
  let ψ := b.equivFun.toLinearMap.comp (φ.comp b.equivFun.symm.toLinearMap)
  let T := LinearMap.toMatrix' ψ
  have hT : T.det = φ.det :=
    (LinearMap.det_toMatrix' ψ).trans (LinearMap.det_conj φ b.equivFun)
  have hψ : Matrix.toLin' T = ψ := Matrix.toLin'_toMatrix' ψ
  have hRange : (LinearMap.range (Matrix.toLin' T)).map b.equivFun.symm.toLinearMap = φ.range := by
    rw [hψ]
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨b.equivFun.symm y, by simp [ψ]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ψ (b.equivFun y), ⟨b.equivFun y, rfl⟩, by simp [ψ]⟩
  let e := Submodule.Quotient.equiv _ _ b.equivFun.symm hRange
  rw [← e.length_eq, ← hT]
  exact matrix_cokerLen_eq_spanLen A (Module.finrank A M) T (hT.symm ▸ hdet)

end LinearMap

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A]
  [Algebra A B] [Module.Free A B] [Module.Finite A B]

/-- The norm of a nonzerodivisor in the original finite free algebra is nonzero. -/
theorem norm_ne_zero_of_isRegular (s : B) (hs : IsRegular s) : norm A s ≠ 0 := by
  intro h
  rw [norm_apply] at h
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) (LinearMap.ker_eq_bot.mpr hs.left)

omit [IsDomain A] [Module.Free A B] [Module.Finite A B] in
private theorem range_lmul_eq_restrictScalars_span (s : B) :
    LinearMap.range (lmul A B s) = (Ideal.span {s}).restrictScalars A := by
  ext x
  simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [Algebra.lmul]⟩

/-- The determinant length is the length of the full principal quotient
over the local scalar ring. -/
theorem length_quotient_span_norm_eq [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (s : B) (hs : IsRegular s) :
    Module.length A (A ⧸ Ideal.span {norm A s}) = Module.length A (B ⧸ Ideal.span {s}) := by
  have h := LinearMap.length_quotient_range_eq_length_quotient_det (lmul A B s)
    (norm_ne_zero_of_isRegular s hs)
  rw [range_lmul_eq_restrictScalars_span s] at h
  exact h.symm

/-- The same norm length formula after localizing at the original prime. The
right side is the localization of the original principal quotient. -/
theorem length_localized_quotient_span_eq_norm [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] [Ring.KrullDimLE 1 (Localization.AtPrime p)]
    (s : B) (hs : IsRegular s) :
    Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) (norm A s)}) =
      Module.length (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (B ⧸ Ideal.span {s})) := by
  let R := Localization.AtPrime p
  let M := LocalizedModule p.primeCompl B
  let : Module.Free R M := Module.free_of_flat_of_isLocalRing
  let φ := lmul A B s
  let ψ := LocalizedModule.map p.primeCompl φ
  have h := ProjectiveDeterminant.det_localization p φ
  rw [ProjectiveDeterminant.det_eq_linearMap_det_of_basis (Module.finBasis A B) φ,
    ProjectiveDeterminant.det_eq_linearMap_det_of_basis (Module.finBasis R M) ψ] at h
  have hDet : algebraMap A R (norm A s) = ψ.det := h
  have hNZ : ψ.det ≠ 0 := by
    rw [← hDet]
    exact (map_ne_zero_iff _ (IsLocalization.injective R p.primeCompl_le_nonZeroDivisors)).2
      (norm_ne_zero_of_isRegular s hs)
  have hRange : φ.range.localized p.primeCompl = ψ.range := by
    exact LinearMap.localized'_range_eq_range_localizedMap (Localization p.primeCompl) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl B) (LocalizedModule.mkLinearMap p.primeCompl B) φ
  let e := (Submodule.quotEquivOfEq _ _ hRange.symm).trans
    (localizedQuotientEquiv p.primeCompl φ.range)
  rw [hDet, ← LinearMap.length_quotient_range_eq_length_quotient_det ψ hNZ, e.length_eq,
    show φ.range = (Ideal.span {s}).restrictScalars A from range_lmul_eq_restrictScalars_span s]
  rfl

end Algebra

section Fibre

universe w

namespace Algebra

variable {A B : Type w} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]

omit [IsDomain A] in
/-- The norm vanishes in the residue field of the image of a point on
which the original element vanishes. -/
theorem norm_mem_comap_of_mem_prime (q : Ideal B) [q.IsPrime] (s : B) (hs : s ∈ q) :
    norm A s ∈ q.comap (algebraMap A B) := by
  let p := q.comap (algebraMap A B)
  let j := algebraMap A p.ResidueField
  let k := algebraMap B q.ResidueField
  let l := Ideal.ResidueField.map p q (algebraMap A B) rfl
  have h : k.comp (algebraMap A B) = l.comp j := by
    ext a
    exact (Ideal.ResidueField.map_algebraMap p q (algebraMap A B) rfl a).symm
  have hz : k s = 0 := by
    change s ∈ RingHom.ker (algebraMap B q.ResidueField)
    rwa [Ideal.ker_algebraMap_residueField]
  have hn := Algebra.projectiveNorm_eq_zero_of_field_hom A j k l h s hz
  rw [Algebra.projectiveNorm_eq_norm_of_free] at hn
  change norm A s ∈ RingHom.ker (algebraMap A p.ResidueField) at hn
  simpa only [Ideal.ker_algebraMap_residueField] using hn

/-- At the original height-one prime the norm length is the sum of the
actual localized quotient lengths weighted by the residue degrees. -/
theorem length_quotient_span_norm_eq_finsum_fibre [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) (s : B) (hs : IsRegular s) :
    Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) (norm A s)}) =
      ∑ᶠ q ∈ {q : PrimeSpectrum B | q.asIdeal.comap (algebraMap A B) = p},
        (Stacks.Length.primeResidueDegree (algebraMap A B) p q.asIdeal : ℕ∞) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (B ⧸ Ideal.span {s})) := by
  classical
  let : Ring.KrullDimLE 1 (Localization.AtPrime p) := (Ring.krullDimLE_iff).2 (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
    exact WithBot.coe_le_coe.2 (le_rfl : (1 : ℕ∞) ≤ 1))
  rw [length_localized_quotient_span_eq_norm p s hs]
  apply Stacks.Length.length_localizedModule_eq_finsum_fibre
  intro q hq hqp
  have hsmul : (Ideal.span {s}) • (⊤ : Submodule B B) = Ideal.span {s} := by
    rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
      Submodule.restrictScalars_self]
  have hq' : q ∈ Module.support B (B ⧸ ((Ideal.span {s}) • (⊤ : Submodule B B))) := by
    rwa [hsmul]
  rw [Module.support_quotient] at hq'
  have hmem : s ∈ q.asIdeal := by
    have hz := hq'.2
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem] at hz
    exact hz
  let r := q.asIdeal.comap (algebraMap A B)
  have hr : norm A s ∈ r := norm_mem_comap_of_mem_prime q.asIdeal s hmem
  by_contra hne
  have hlt : r < p := lt_of_le_of_ne hqp hne
  let : p.FiniteHeight := by simp [Ideal.finiteHeight_iff, hp]
  have hh : r.height < 1 := hp ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  have hbot : r = ⊥ := Ideal.height_eq_zero_iff_eq_bot.1 (Order.lt_one_iff.mp hh)
  exact norm_ne_zero_of_isRegular s hs (by simpa only [hbot, Ideal.mem_bot] using hr)

end Algebra

end Fibre
