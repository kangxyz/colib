/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.AuxiliaryQuadraticParameter
public import Colib.RingTheory.Bertini.WholeFiberParameterOpen
public import Colib.RingTheory.Bertini.QuadraticSelectedEtaleOpen
public import Colib.RingTheory.Bertini.QuadraticClosedInfinityAvoidance

/-! # Simultaneous whole-fiber, étale and full infinity conditions before one choice

Both selected determinants, every off-diagonal relation and both infinity
conditions are combined in the same augmented coefficient ring. Only then is
one ground-field tuple chosen. No compactifying row is fixed in advance.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial AlgebraicGeometry
universe u
namespace QuadraticIncidence

/-- Include a condition on the unchanged tail rows into the full coefficient space. -/
def tailParameterPolynomial (k : Type u) [CommRing k] {N : Type u} (d : ℕ) :
    MvPolynomial (Fin d × N) k →ₐ[k] MvPolynomial (Fin (d + 1) × N) k :=
  rename (fun q => (q.1.succ, q.2))

theorem tailParameterPolynomial_ne_zero (k : Type u) [CommRing k] {N : Type u}
    (d : ℕ) (q : MvPolynomial (Fin d × N) k) (hq : q ≠ 0) :
    tailParameterPolynomial k d q ≠ 0 := by
  apply (rename_eq_zero_iff_of_injective q ?_).not.mpr hq
  intro x y h
  apply Prod.ext
  · exact Fin.succ_injective d (congrArg Prod.fst h)
  · exact congrArg (fun z : Fin (d + 1) × N => z.2) h

@[simp] theorem eval_tailParameterPolynomial (k : Type u) [CommRing k] {N : Type u}
    (d : ℕ) (a : N → k) (c : Fin d × N → k)
    (q : MvPolynomial (Fin d × N) k) :
    eval (prependParameters k d a c) (tailParameterPolynomial k d q) = eval c q := by
  rw [tailParameterPolynomial, eval_rename]
  rfl

/-- The universal nonempty full parameter open retains the full original bad
ideal, whole projection fiber, and actual selected-point étale neighborhood. -/
theorem exists_wholeFiber_etale_infinity_open (k R : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ H : MvPolynomial (Fin (d + 1) × Exponent σ) k, H ≠ 0 ∧
      ∀ (a : Exponent σ → k) (c : Fin d × Exponent σ → k),
      eval (prependParameters k d a c) H ≠ 0 →
      eval c q ≠ 0 ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      (∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun i => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  have hd' : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hd.le
  obtain ⟨F, hF, hwhole⟩ := InfinityChart.exists_infinity_avoidance_polynomial k R g d hd'
  obtain ⟨Z, hZ, hclosed⟩ :=
    InfinityChart.exists_closed_infinity_avoidance_polynomial k R I hI g d hd'
  obtain ⟨E, hE, hetale⟩ := exists_selectedEtale_open k R P g hg (d + 1) hd
  obtain ⟨W, hW, hsmooth⟩ := exists_wholeFiber_smooth_open k R P g hg d hd
  refine ⟨(F * E) * tailParameterPolynomial k d ((W * Z) * q),
    mul_ne_zero (mul_ne_zero hF hE)
      (tailParameterPolynomial_ne_zero k d _ (mul_ne_zero (mul_ne_zero hW hZ) hq)), ?_⟩
  intro a c hc
  simp only [map_mul, eval_tailParameterPolynomial, mul_ne_zero_iff] at hc
  exact ⟨hc.2.2, hwhole _ hc.1.1, hclosed c hc.2.1.2,
    hetale _ hc.1.2, hsmooth c hc.2.1.1⟩

/-- One actual ground tuple is chosen only after all conditions have been
combined. The auxiliary row and every original tail row are parts of that tuple. -/
theorem exists_wholeFiber_etale_closed_infinity (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      (∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun i => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨H, hH, hgood⟩ := exists_wholeFiber_etale_infinity_open k R P I hI g hg d hd q hq
  have hex : ∃ b : Fin (d + 1) × Exponent σ → k, eval b H ≠ 0 := by
    by_contra! h
    exact hH (MvPolynomial.funext fun b => by simpa using h b)
  obtain ⟨b, hb⟩ := hex
  let a := fun e => b (0, e)
  let c := fun e : Fin d × Exponent σ => b (e.1.succ, e.2)
  have he : prependParameters k d a c = b := by
    funext z
    rcases z with ⟨i, e⟩
    exact Fin.cases rfl (fun _ => rfl) i
  exact ⟨a, c, hgood a c (he.symm ▸ hb)⟩

end QuadraticIncidence
