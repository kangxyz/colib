/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Kaehler.ScalarResidueGradient
import Colib.RingTheory.Bertini.ScalarMovingCoefficientMap
import Colib.RingTheory.Polynomial.Residue.FiberEvaluation

open Module KaehlerDifferential
open scoped TensorProduct

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

example (k R L K : Type u) [CommRing k] [CommRing R] [CommRing L] [CommRing K]
    [Algebra k R] [Algebra k L] [Algebra (R ⊗[k] L) K]
    [Algebra R K] [IsScalarTower R (R ⊗[k] L) K] (a : K) (r : R) :
    scalarResidueEquiv k R L K (a ⊗ₜ[R] D k R r) =
      a ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L) (algebraMap R (R ⊗[k] L) r) :=
  scalarResidueEquiv_tmul_D k R L K a r

noncomputable example (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {ι : Type v} (B : Basis ι x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k])) :
    Basis ι y.asIdeal.ResidueField
      (y.asIdeal.ResidueField ⊗[R ⊗[k] L] Ω[(R ⊗[k] L)⁄L]) :=
  scalarClosedPointCotangentBasis k R L x y hy B

example (k R L K : Type u) [CommRing k] [CommRing R] [CommRing L] [CommRing K]
    [Algebra k R] [Algebra k L] [Algebra (R ⊗[k] L) K]
    [Algebra R K] [IsScalarTower R (R ⊗[k] L) K]
    {σ : Type u} [Fintype σ] {ι : Type v}
    (g : σ → R) (c : ι → σ → K)
    (h : LinearIndependent K (fun i => residueGeneratorGradient k R K g (c i))) :
    LinearIndependent K (fun i => residueGeneratorGradient L (R ⊗[k] L) K
      (algebraMap R (R ⊗[k] L) ∘ g) (c i)) :=
  independent_scalarResidueGradient k R L K g c h

example (k κ L K : Type u) [Field k] [Field κ] [Field L] [Field K]
    [Algebra k κ] [Algebra k L] [Algebra k K] [Algebra L K] [Algebra κ K]
    [IsScalarTower k L K] [IsScalarTower k κ K]
    {τ : Type u} (T : MvPolynomial τ κ) (c : τ → L)
    (hu : let : Algebra (MvPolynomial τ k) L :=
        (MvPolynomial.eval₂Hom (algebraMap k L) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial τ k] (MvPolynomial.residueCoefficientEquiv k κ τ).symm T :
        L ⊗[MvPolynomial τ k] (MvPolynomial τ k ⊗[k] κ))) :
    MvPolynomial.eval₂ (algebraMap κ K) (algebraMap L K ∘ c) T ≠ 0 :=
  MvPolynomial.eval₂_ne_zero_of_isUnit_residueFiber k κ L K T c hu
