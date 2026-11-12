/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Bertini.LargePrimeQuadraticEtaleInfinity
public import Colib.RingTheory.Bertini.ScalarWholeFiberSmoothProjection
public import Colib.RingTheory.Bertini.MovingPointParameterAvoidance

/-! # One actual two-prime choice carries infinity, étale and whole-fiber smoothness

The original cotangent basis, common bad-chart relation and infinity polynomials
are constructed before the same two finite scalar fields are selected. All
conditions concern one unchanged scalar tuple and the full mapped ideal.
Finiteness of its coordinate maps is a separate theorem, not inferred here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Module TensorProduct KaehlerDifferential _root_.MvPolynomial AlgebraicGeometry
open scoped TensorProduct

namespace QuadraticIncidence.InfinityChart

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The same large finite extensions and original monomial tuple simultaneously
retain all original closed-fiber points, every scalar minimal component of I,
and every point of the selected projection fiber. No basis, parameter relation,
finite-coordinate map, smoothness conclusion or presentation family is supplied. -/
theorem exists_two_prime_wholeFiber_infinity_parameters
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, N < n ∧ N < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        let S := R ⊗[k] L
        let gS := algebraMap R S ∘ g
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap R S) y = x ∧
            (∀ z : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) z = x → z = y) ∧
            y.asIdeal.IsMaximal ∧ Algebra.adjoin L (Set.range gS) = ⊤ ∧
            ∃ (a : Exponent σ → L) (c : Fin d × Exponent σ → L),
              eval₂ (algebraMap k L) c q ≠ 0 ∧
              NoCommonInfinityZero L S gS d (prependParameters L d a c) ∧
              NoCommonClosedInfinityZero L S (I.map (algebraMap R S)) gS d c ∧
              (∀ (z : PrimeSpectrum S), PrimeSpectrum.comap (algebraMap R S) z = x →
                ∃ s ∉ z.asIdeal, ((algebraMap S (Localization.Away s)).comp
                  (aeval (R := L) (fun i =>
                    aeval gS (parameterTuple L σ (d + 1)
                      (prependParameters L d a c) i).val)).toRingHom).Etale) ∧
              ∀ (Q : PrimeSpectrum S),
                Ideal.comap (aeval (R := L) (fun i =>
                  aeval gS (parameterTuple L σ d c i).val)).toRingHom y.asIdeal =
                Ideal.comap (aeval (R := L) (fun i =>
                  aeval gS (parameterTuple L σ d c i).val)).toRingHom Q.asIdeal →
                ∃ s ∉ Q.asIdeal, SmoothOfRelativeDimension 1
                  (Spec.map (CommRingCat.ofHom ((algebraMap S (Localization.Away s)).comp
                    (aeval (R := L) (fun i =>
                      aeval gS (parameterTuple L σ d c i).val)).toRingHom))) := by
  have hrank : Module.finrank x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]) = d + 1 := by
    rw [Algebra.cotangent_finrank_eq_trdeg_toNat k R x.asIdeal.ResidueField, hd]
    simp
  let B := Module.finBasisOfFinrankEq x.asIdeal.ResidueField
    (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]) hrank
  obtain ⟨f, hf, hz⟩ := MovingPointChart.exists_nonzero_common_parameter_relation k R
    (ClosedPoint.CoefficientRing k R x) g hg
    (fun j => ClosedPoint.selectedValue k R x (g j)) d hd
  have hd' : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hd.le
  obtain ⟨n, m, hn, hm, hnm, h⟩ := exists_two_prime_quadratic_etale_infinity
    k R p x I hI g hg d hd' B f q hf hq N
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdeg, hdom, hyunique, a, c, hf', hq', hW, hZ, hD, he⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  let S := R ⊗[k] L
  let gS := algebraMap R S ∘ g
  let : IsDomain S := hdom
  obtain ⟨y, hy, hyunique⟩ := hyunique
  have hxy : y.asIdeal.under R = x.asIdeal := congrArg PrimeSpectrum.asIdeal hy
  have hymax : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := R) (S := S) y.asIdeal (by rw [hxy]; infer_instance)
  have hgS : Algebra.adjoin L (Set.range gS) = ⊤ := by
    let e := Algebra.TensorProduct.commRight k L R
    have ht := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k) (A := L) (Set.range g) hg
    have hm := congrArg (Subalgebra.map e.toAlgHom) ht
    rw [← Algebra.adjoin_image, Algebra.map_top,
      (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective] at hm
    have hset : e '' ((fun z : R => (1 : L) ⊗ₜ[k] z) '' Set.range g) = Set.range gS := by
      rw [← Set.image_comp, ← Set.range_comp]
      rfl
    change Algebra.adjoin L
      (e '' ((fun z : R => (1 : L) ⊗ₜ[k] z) '' Set.range g)) = ⊤ at hm
    rw [hset] at hm
    exact hm
  refine ⟨hdeg, hdom, y, hy, hyunique, hymax, hgS, a, c, hq', hW, hZ, he, ?_⟩
  intro Q hQ
  exact exists_scalar_wholeFiber_smooth_projection k R L x y hy
    g hg d B f c hf' hz hD hd Q hQ

end QuadraticIncidence.InfinityChart
