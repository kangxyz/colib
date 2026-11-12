/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousFiniteCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FiniteCoordinates
public import Colib.AlgebraicGeometry.Normalization.Compactification.NonemptyBoundary

/-!
# The same étale tuple and its retained normal proper curve

Keep the full tuple's actual étale principal neighborhood when applying the finite-coordinate
compactification producer. The étale chart and relative curve therefore use the same auxiliary
row and tail coordinates; neither is reselected. This strengthens the output retained by the
adjacent good-neighborhood supplier without changing it.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- A single generated tuple gives both its actual étale principal chart at the selected point
and the normal proper relative-curve compactification with finite full retained boundary. -/
theorem exists_simultaneous_etale_good_quadratic_neighborhood (k B : Type u) [Field k] [Infinite k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (P : PrimeSpectrum B) [P.asIdeal.IsMaximal] (I : Ideal B) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k) (r : B), eval c q ≠ 0 ∧
    r - 1 ∈ Ideal.map (quadraticCoordinateHom k B g d c)
      (Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal) ∧
    (∀ Q : PrimeSpectrum B,
      Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal =
        Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
    (∃ rₑ ∉ P.asIdeal, ((algebraMap B (Localization.Away rₑ)).comp
      (aeval (R := k) (fun j => aeval g
        (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom).Etale) ∧
    let R := MvPolynomial (Fin d) k
    let f := quadraticRelativeCoordinateHom k B g d a c
    let W : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen r
    let s := Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) P
    let Z := Spec (.of (B ⧸ I))
    let z : Z ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N) (π : N ⟶ projectiveLine R)
      (b : D ⟶ N) (e : D ⟶ Spec (.of R)) (t : R) (hi : IsOpenImmersion i),
      letI := hi;
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsFinite π ∧ Surjective π ∧ IsProper (π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsClosedImmersion b ∧ IsFinite (b ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsPullback b e π (projectiveLineInfinitySection R) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom f) ≫ projectiveLineXChart R ∧
      i ≫ π ≫ (projectiveLine R ↘ Spec (.of R)) =
        Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) ∧
      s ∈ PrimeSpectrum.basicOpen t ∧ IsAffine (i ''ᵁ W).toScheme ∧
      SmoothOfRelativeDimension 1 ((i ''ᵁ W).ι ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsFinite ((retainedBoundaryInclusion (i ''ᵁ W) ≫ π ≫
        (projectiveLine R ↘ Spec (.of R))) ∣_ PrimeSpectrum.basicOpen t) ∧
      IsAffine ((((i ''ᵁ W).ι ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen t).toScheme) ∧
      ∀ x : Z, (z ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C))) x ∈
        PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ W := by
  obtain ⟨a, c, hc, hZ, hf, he, r, hr, hW, ha, hsm⟩ :=
    exists_simultaneous_finite_quadratic_coordinates k B P I hI g hg d hd q hq
  have hbase := quadraticRelativeCoordinateHom_comp_C k B g d a c
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) := ha
  have : SmoothOfRelativeDimension 1
      (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
        Spec.map (CommRingCat.ofHom ((quadraticRelativeCoordinateHom k B g d a c).comp
          Polynomial.C))) := by rw [hbase]; exact hsm
  have : IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom ((quadraticRelativeCoordinateHom k B g d a c).comp
        Polynomial.C))) := by
    rw [hbase, ← Spec.map_comp]
    exact hZ
  obtain ⟨N, D, i, π, b, e, t, hi, hN, hn, hnormal, hπ, hp, hb, hfinite, hpb,
    hrange, hfac, hbase', ht, ha', hsm', hnew, ha'', hz⟩ :=
    exists_good_neighborhood_of_finite_polynomial_coordinates k
    (MvPolynomial (Fin d) k) B (quadraticRelativeCoordinateHom k B g d a c) hf
    (PrimeSpectrum.basicOpen r)
      (Spec.map (CommRingCat.ofHom ((quadraticRelativeCoordinateHom k B g d a c).comp
        Polynomial.C)) P)
      (by
        intro Q hQ
        apply hW Q
        have h := congrArg PrimeSpectrum.asIdeal hQ.symm
        change Ideal.comap ((quadraticRelativeCoordinateHom k B g d a c).comp Polynomial.C)
          P.asIdeal = Ideal.comap
            ((quadraticRelativeCoordinateHom k B g d a c).comp Polynomial.C) Q.asIdeal at h
        rw [hbase] at h
        exact h) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have := hπ
  have hsurj : Surjective π := by
    obtain ⟨rₑ, hrₑ, heₑ⟩ := he
    apply Scheme.surjective_projectiveLine_cover_of_etale_away
      (MvPolynomial (Fin d) k) B (quadraticRelativeCoordinateHom k B g d a c)
      rₑ (fun hzero => hrₑ (hzero ▸ P.asIdeal.zero_mem)) _ i π hfac
    exact relativeCoordinateHom_etale_away k B d _ rₑ heₑ
  exact ⟨a, c, r, hc, hr, hW, he, N, D, i, π, b, e, t, hi, hN, hn, hnormal,
    hπ, hsurj, hp, hb, hfinite, hpb, hrange, hfac, hbase', ht, ha', hsm', hnew, ha'', hz⟩

end QuadraticIncidence.InfinityChart
