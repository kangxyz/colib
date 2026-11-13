/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Zero
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeChart
public import Colib.RingTheory.Polynomial.LaurentPowerCut
public import Colib.RingTheory.Polynomial.LaurentPowerCutFamily

/-!
# Finite zero schemes for Laurent power cuts

A support finite over the native torus over an affine scheme has finite cuts
by the equations `t ^ n - u` for large `n`, and by `t ^ n - 1` for positive `n`.
The numerator of the interpolation between two power cuts has finite zero
scheme under the same large-exponent condition, uniformly in its coefficient.
The zero schemes are the actual affine-line fibres of the indicated sections.

See Voevodsky, *Cancellation theorem*, Lemma 4.1 and Remark 4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber

set_option backward.isDefEq.respectTransparency false in
private theorem isFinite_comp_of_finite_section_quotient {X P Z : Scheme.{u}}
    [IsAffine X] [IsAffine P] (i : Z ⟶ P) [IsClosedImmersion i] (p : P ⟶ X)
    (s : Γ(P, ⊤)) (hs : i.appTop s = 0)
    (h : ((Ideal.Quotient.mk (Ideal.span {s})).comp p.appTop.hom).Finite) :
    IsFinite (i ≫ p) := by
  let I : Ideal Γ(P, ⊤) := Ideal.span {s}
  let φ : Γ(P, ⊤) ⧸ I →+* Γ(Z, ⊤) := Ideal.Quotient.lift I i.appTop.hom <|
    show I ≤ RingHom.ker i.appTop.hom from Ideal.span_le.mpr fun r hr => by
      change i.appTop r = 0
      rwa [Set.mem_singleton_iff.mp hr]
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨r, hr⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 z
    exact ⟨Ideal.Quotient.mk I r, hr⟩
  have he : φ.comp ((Ideal.Quotient.mk I).comp p.appTop.hom) = (i ≫ p).appTop.hom := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    ext r
    rfl
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite.{u})]
  refine ⟨?_, ?_⟩
  · exact isAffine_of_isAffineHom i
  · rw [← he]
    exact (RingHom.Finite.of_surjective φ hφ).comp h

private theorem isFinite_section_zero_of_finite_quotient {k R : Type u} [Field k]
    [CommRing R] {P : Scheme.{u}} [IsAffine P]
    (b : P ⟶ Spec (.of k)) (p : P ⟶ Spec (.of R)) (s : Γ(P, ⊤))
    (h : ((Ideal.Quotient.mk (Ideal.span {s})).comp
      (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom)).Finite) :
    IsFinite (inclusion (sectionToAffineLine b s) 0 ≫ p) := by
  apply isFinite_comp_of_finite_section_quotient _ p s (section_zero_inclusion_appTop b s)
  have hinv : ((ΓSpecIso (.of R)).inv.hom.comp (ΓSpecIso (.of R)).hom.hom) = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have hf := h.comp <| RingHom.Finite.of_surjective (ΓSpecIso (.of R)).hom.hom
    (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).hom).2
  rwa [RingHom.comp_assoc, RingHom.comp_assoc, hinv, RingHom.comp_id] at hf

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme

variable {k R : Type u} [Field k] [CommRing R]
  (f : Spec (.of R) ⟶ Spec (.of k)) {P : Scheme.{u}} (g : P ⟶ ambient f)

set_option quotPrecheck false in
local notation "p" => (g ≫ pullback.fst f
  (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)))
set_option quotPrecheck false in
local notation "t" => g.appTop (ambientCoordinate f).val
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)
set_option quotPrecheck false in
local notation "C" => (p).appTop.hom.comp (ΓSpecIso (.of R)).inv.hom
set_option quotPrecheck false in
local notation "L" => g.appTop.hom.comp (chartRingHom f)
local notation "cut(" s ")" =>
  Scheme.AffineLineFiber.inclusion (sectionToAffineLine (p ≫ f) s) 0 ≫ p

private theorem finite_chartRingHom [IsFinite g] : (L).Finite := by
  let : IsIso (chartInverse f) := inferInstanceAs (IsIso (nativeChartIso f).inv)
  have h := ((g ≫ chartInverse f).finite_appTop).comp <|
    RingHom.Finite.of_surjective (ΓSpecIso (.of (LaurentPolynomial R))).inv.hom
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of (LaurentPolynomial R))).inv).2
  rw [Scheme.Hom.comp_appTop, ← CommRingCat.hom_comp, ← Category.assoc,
    chartInverse_appTop, CommRingCat.hom_comp] at h
  exact h

private theorem chartRingHom_power (n : ℕ) : L (LaurentPolynomial.T (n : ℤ)) = t ^ n := by
  rw [← mul_one (n : ℤ), ← LaurentPolynomial.T_pow, map_pow]
  simp only [RingHom.comp_apply, chartRingHom_T]

private theorem chartRingHom_coefficient (r : R) : L (LaurentPolynomial.C r) = C r := by
  simp only [RingHom.comp_apply, chartRingHom_C, ambientCoefficient, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

private theorem isFinite_cut_of_finite_quotient [IsFinite g] {s : Aₚ}
    (h : ((Ideal.Quotient.mk (Ideal.span {s})).comp C).Finite) : IsFinite (cut(s)) := by
  let : IsIso (chartInverse f) := inferInstanceAs (IsIso (nativeChartIso f).inv)
  let : IsAffine P := isAffine_of_isAffineHom (g ≫ chartInverse f)
  exact isFinite_section_zero_of_finite_quotient (p ≫ f) p s h

/-- On a support finite over the native torus over `Spec R`, the actual zero scheme
of `t ^ n - u` is finite over `Spec R` for all large `n`. -/
theorem exists_isFinite_power_sub_unit [IsFinite g] (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsFinite (cut(t ^ n - (u₀ : Aₚ))) := by
  let : Algebra R Aₚ := (C).toAlgebra
  let : Algebra (LaurentPolynomial R) Aₚ := (L).toAlgebra
  let : IsScalarTower R (LaurentPolynomial R) Aₚ :=
    IsScalarTower.of_algebraMap_eq (fun r => (chartRingHom_coefficient f g r).symm)
  let : Module.Finite (LaurentPolynomial R) Aₚ := finite_chartRingHom f g
  obtain ⟨N, hN⟩ := LaurentPolynomial.exists_moduleFinite_quotient_span_T_sub_unit R u₀
  refine ⟨N, fun n hn => isFinite_cut_of_finite_quotient f g ?_⟩
  have h := hN n hn
  change Module.Finite R (Aₚ ⧸ Ideal.span {L (LaurentPolynomial.T (n : ℤ)) - (u₀ : Aₚ)}) at h
  rw [chartRingHom_power f g n] at h
  exact h

/-- On a support finite over the native torus over `Spec R`, the actual zero scheme
of `t ^ n - 1` is finite over `Spec R` for positive `n`. -/
theorem isFinite_power_sub_one [IsFinite g] {n : ℕ} (hn : 0 < n) :
    IsFinite (cut(t ^ n - (1 : Aₚ))) := by
  let : Algebra R Aₚ := (C).toAlgebra
  let : Algebra (LaurentPolynomial R) Aₚ := (L).toAlgebra
  let : IsScalarTower R (LaurentPolynomial R) Aₚ :=
    IsScalarTower.of_algebraMap_eq (fun r => (chartRingHom_coefficient f g r).symm)
  let : Module.Finite (LaurentPolynomial R) Aₚ := finite_chartRingHom f g
  have h := LaurentPolynomial.moduleFinite_quotient_span_T_sub_one R (B := Aₚ) hn
  change Module.Finite R (Aₚ ⧸ Ideal.span {L (LaurentPolynomial.T (n : ℤ)) - (1 : Aₚ)}) at h
  rw [chartRingHom_power f g n] at h
  exact isFinite_cut_of_finite_quotient f g h

/-- The actual zero scheme of the interpolated numerator is finite over `Spec R`
for two large exponents, uniformly in the coefficient of the interpolation. -/
theorem exists_isFinite_power_cut_family [IsFinite g] (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → ∀ a : R,
      IsFinite (cut(C a * (t ^ m - 1) * (t ^ n - (u₀ : Aₚ)) +
        (1 - C a) * (t ^ n - 1) * (t ^ m - (u₀ : Aₚ)))) := by
  let : Algebra R Aₚ := (C).toAlgebra
  let : Algebra (LaurentPolynomial R) Aₚ := (L).toAlgebra
  let : IsScalarTower R (LaurentPolynomial R) Aₚ :=
    IsScalarTower.of_algebraMap_eq (fun r => (chartRingHom_coefficient f g r).symm)
  let : Module.Finite (LaurentPolynomial R) Aₚ := finite_chartRingHom f g
  obtain ⟨N, hN⟩ := LaurentPolynomial.exists_moduleFinite_quotient_span_powerCutFamilyEquation
    R u₀
  refine ⟨N, fun m n hm hn a => isFinite_cut_of_finite_quotient f g ?_⟩
  have h := hN m n hm hn a
  change Module.Finite R (Aₚ ⧸ Ideal.span {
    C a * (L (LaurentPolynomial.T (m : ℤ)) - 1) * (L (LaurentPolynomial.T (n : ℤ)) - (u₀ : Aₚ)) +
    (1 - C a) * (L (LaurentPolynomial.T (n : ℤ)) - 1) *
      (L (LaurentPolynomial.T (m : ℤ)) - (u₀ : Aₚ))}) at h
  rwa [chartRingHom_power f g m, chartRingHom_power f g n] at h

end AlgebraicGeometry.NativeTorusPolynomial
