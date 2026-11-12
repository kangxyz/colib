/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.QuadraticDiagonalFieldExtension
public import Colib.RingTheory.Bertini.MovingPointTupleAvoidance
public import Colib.RingTheory.Bertini.CommonResidueFieldExtension
public import Colib.RingTheory.Kaehler.PolynomialResidueGradient
public import Colib.RingTheory.Kaehler.ResidueIndependentSmoothMap
public import Colib.RingTheory.Polynomial.OriginalFunctionEvaluation

/-! # One nonempty parameter open controls the entire original projection fiber

The selected-point determinant and the common moving-point relation are formed
before choosing any coefficients. No infinite-field assumption is needed for
this open. Every point of the full projection fiber is handled through a common
residue field, including nonclosed points and nonrational selected points.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial AlgebraicGeometry
universe u
namespace QuadraticIncidence

/-- A single ground polynomial controls both diagonal and off-diagonal points
of the literal original quadratic tuple over every coefficient-algebra field. -/
theorem exists_wholeFiber_parameter_open (k R : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ (c : Fin d × Exponent σ → k), eval c q ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K]
        [Algebra (ClosedPoint.CoefficientRing k R p) K]
        [IsScalarTower k (ClosedPoint.CoefficientRing k R p) K]
        [IsScalarTower R (ClosedPoint.CoefficientRing k R p) K],
        (∀ i, eval (fun j => algebraMap R K (g j))
            (parameterTuple K σ d (algebraMap k K ∘ c) i).val =
          eval (fun j => algebraMap (ClosedPoint.CoefficientRing k R p) K
            (ClosedPoint.selectedValue k R p (g j)))
            (parameterTuple K σ d (algebraMap k K ∘ c) i).val) →
        LinearIndependent K (fun i => residueGeneratorGradient k R K g
          (fun j => eval (fun l => algebraMap R K (g l))
            (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
  have hrank : Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] Ω[R⁄k]) = d + 1 := by
    rw [Algebra.cotangent_finrank_eq_trdeg_toNat k R p.asIdeal.ResidueField, hd]
    simp
  obtain ⟨q₀, hq₀, hselected⟩ := exists_selectedPoint_open
    (L := p.asIdeal.ResidueField) g hg d hrank
  obtain ⟨f, hf, hoff⟩ := MovingPointChart.exists_nonzero_offDiagonal_parameterTuple_open
    k R (ClosedPoint.CoefficientRing k R p) g hg
    (fun j => ClosedPoint.selectedValue k R p (g j)) d hd
  refine ⟨q₀ * f, mul_ne_zero hq₀ hf, ?_⟩
  intro c hc K _ _ _ _ _ _ hvalue
  rw [map_mul] at hc
  by_cases he : (fun j => algebraMap R K (g j)) =
      fun j => algebraMap (ClosedPoint.CoefficientRing k R p) K
        (ClosedPoint.selectedValue k R p (g j))
  · exact ClosedPoint.independent_parameterTuple_at_diagonal k R p K g hg d c
      (hselected c (mul_ne_zero_iff.mp hc).1) (fun j => congrFun he j)
  · exact hoff c (mul_ne_zero_iff.mp hc).2 K he hvalue

/-- The parameter-open assertion is transported to the actual original
functions and differentials, not merely a formal coordinate matrix. -/
theorem exists_wholeFiber_originalFunctions_open (k R : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ (c : Fin d × Exponent σ → k), eval c q ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K]
        [Algebra (ClosedPoint.CoefficientRing k R p) K]
        [IsScalarTower k (ClosedPoint.CoefficientRing k R p) K]
        [IsScalarTower R (ClosedPoint.CoefficientRing k R p) K],
        (∀ i, eval (fun j => algebraMap R K (g j))
            (parameterTuple K σ d (algebraMap k K ∘ c) i).val =
          eval (fun j => algebraMap (ClosedPoint.CoefficientRing k R p) K
            (ClosedPoint.selectedValue k R p (g j)))
            (parameterTuple K σ d (algebraMap k K ∘ c) i).val) →
        LinearIndependent K (fun i =>
          (1 : K) ⊗ₜ[R] D k R (aeval g (parameterTuple k σ d c i).val)) := by
  obtain ⟨q, hq, h⟩ := exists_wholeFiber_parameter_open k R p g hg d hd
  refine ⟨q, hq, ?_⟩
  intro c hc K _ _ _ _ _ _ hv
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq'
    ((IsScalarTower.algebraMap_eq k (ClosedPoint.CoefficientRing k R p) K).trans
      (by rw [IsScalarTower.algebraMap_eq k R (ClosedPoint.CoefficientRing k R p),
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R
          (ClosedPoint.CoefficientRing k R p) K]))
  have hi := h c hc K hv
  simpa only [← parameterTuple_map,
    residueGeneratorGradient_map_polynomial] using hi

/-- On one fixed nonempty parameter open, every prime in the full selected
fiber has a genuine principal neighborhood smooth of relative dimension one.
The open is constructed before any ground coefficient choice. -/
theorem exists_wholeFiber_smooth_open (k R : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ (c : Fin d × Exponent σ → k), eval c q ≠ 0 →
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨q, hq, hfield⟩ := exists_wholeFiber_originalFunctions_open k R P g hg d hd
  refine ⟨q, hq, ?_⟩
  intro c hc
  let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
  dsimp only
  intro Q hPQ
  apply exists_smooth_one_of_residue_independent k R Q.asIdeal d f hd
  apply independent_differentials_of_same_fiber k R P Q d f hPQ
  intro K _ _ _ _ _ _ hv
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq'
    ((IsScalarTower.algebraMap_eq k (ClosedPoint.CoefficientRing k R P) K).trans
      (by rw [IsScalarTower.algebraMap_eq k R (ClosedPoint.CoefficientRing k R P),
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R
          (ClosedPoint.CoefficientRing k R P) K]))
  let s : R →ₐ[k] K := (IsScalarTower.toAlgHom k (ClosedPoint.CoefficientRing k R P) K).comp
    ((Algebra.TensorProduct.includeRight : P.asIdeal.ResidueField →ₐ[k]
      ClosedPoint.CoefficientRing k R P).comp
        (IsScalarTower.toAlgHom k R P.asIdeal.ResidueField))
  apply hfield c hc K
  intro i
  rw [← parameterTuple_map, eval_map_generator_polynomial]
  change algebraMap R K (f i) = eval (fun j => s (g j))
    (MvPolynomial.map (algebraMap k K) (parameterTuple k σ d c i).val)
  rw [eval_map_original_function]
  exact hv i

end QuadraticIncidence
