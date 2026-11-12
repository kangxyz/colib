/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.QuadraticValuationBoundary
public import Colib.RingTheory.Bertini.QuadraticRelativeCoordinates
public import Colib.RingTheory.IntegralClosure.ValuativeCriterion

/-! # Actual finite quadratic coordinates from original infinity avoidance

No finite map is supplied as a premise. Every valuation ring containing the
chosen coordinate algebra contains the original affine generators. The native
integral-closure criterion and finite type then prove finiteness of that exact
coordinate homomorphism, without a projective model or a coordinate change.
-/
@[expose] public noncomputable section

open _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- The original coordinate map is finite for any number of rows, including zero,
when those rows have no common zero on any full original infinity chart. -/
theorem quadraticCoordinateHom_finite_of_no_infinity
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin d × Exponent σ → k)
    (h : ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra (boundaryRing k R g j) K]
        [IsScalarTower k (boundaryRing k R g j) K],
        ¬ ProjectiveEvaluationIncidence.Vanishes k (boundaryRing k R g j) K
          (boundaryCoordinate k R g j) d c) :
    (quadraticCoordinateHom k R g d c).Finite := by
  let F := FractionRing R
  let φ := quadraticCoordinateHom k R g d c
  let f : MvPolynomial (Fin d) k →+* F := (algebraMap R F).comp φ
  have hint : φ.IsIntegral := by
    intro x
    apply RingHom.IsIntegralElem.of_map (IsFractionRing.injective R F)
    apply f.isIntegralElem_of_mem_valuationSubrings (algebraMap R F x)
    intro V hV
    have hk : ∀ a : k, algebraMap k F a ∈ V := by
      intro a
      apply hV
      refine ⟨C a, ?_⟩
      simp [f, φ, quadraticCoordinateHom, IsScalarTower.algebraMap_apply k R F]
    have hc : ∀ i : Fin d, algebraMap R F
        (aeval g (parameterTuple k σ d c i).val) ∈ V := by
      intro i
      exact hV ⟨X i, by simp [f, φ, quadraticCoordinateHom]⟩
    have hm := monomial_mem_valuationSubring_of_no_infinity k R g d c h V hk hc
    let T : Subalgebra k R :=
      { __ := (V.toSubring.comap (algebraMap R F)).toSubsemiring
        algebraMap_mem' := fun a => by
          change algebraMap R F (algebraMap k R a) ∈ V
          simpa only [← IsScalarTower.algebraMap_apply k R F] using hk a }
    have hgen : Algebra.adjoin k (Set.range g) ≤ T := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact (monomialFunction_linear k R g i) ▸ hm (linearIndex i)
    rw [hg] at hgen
    exact hgen (show x ∈ (⊤ : Subalgebra k R) from trivial)
  have hsurj : Function.Surjective (aeval (R := k) g) := by
    apply (AlgHom.range_eq_top _).mp
    rwa [aeval_range]
  let : Algebra.FiniteType k R := Algebra.FiniteType.of_surjective (aeval g) hsurj
  have hφC : φ.comp (C : k →+* MvPolynomial (Fin d) k) = algebraMap k R := by
    ext a
    simp [φ, quadraticCoordinateHom]
  have hft : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := (C : k →+* MvPolynomial (Fin d) k))
    rw [hφC]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact hint.to_finite hft

/-- The auxiliary polynomial variable and all original tail coordinates give a
finite map to the actual relative affine line. -/
theorem quadraticRelativeCoordinateHom_finite
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (h : NoCommonInfinityZero k R g d (prependParameters k d a c)) :
    (quadraticRelativeCoordinateHom k R g d a c).Finite := by
  apply relativeCoordinateHom_finite
  exact quadraticCoordinateHom_finite_of_no_infinity k R g (d + 1) hg
    (prependParameters k d a c) h

end QuadraticIncidence.InfinityChart
