/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousPrincipalQuadraticParameters
public import Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ClosedProjectionFinite
public import Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.RelativeCoordinates

/-! # The same generated parameters give finite original coordinates and a whole smooth fiber

No replacement of the tuple by Noether normalization is made. The actual graph's
absence of infinity proves finiteness, including the prescribed nonreduced closed scheme.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial AlgebraicGeometry CategoryTheory
universe u
namespace QuadraticIncidence

/-- The generated auxiliary row and base rows simultaneously provide the finite polynomial
map, the finite prescribed closed subscheme, and one smooth affine whole-fiber neighborhood. -/
@[colib_tag "COL-1076"]
theorem exists_simultaneous_finite_quadratic_coordinates (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (InfinityChart.quadraticCoordinateHom k R g d c)))) ∧
      (InfinityChart.quadraticRelativeCoordinateHom k R g d a c).Finite ∧
      (∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun i => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∃ r : R,
        r - 1 ∈ Ideal.map (aeval (R := k) f).toRingHom
          (Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal) ∧
        (∀ Q : PrimeSpectrum R,
          Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
            Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (aeval (R := k) f).toRingHom)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨a, c, hc, hZ, hW, he, hs⟩ := exists_simultaneous_principal_quadratic_parameters
    k R P I hI g hg d hd q hq
  have hf := InfinityChart.quadraticTupleMap_isFinite k R g d hg
    (prependParameters k d a c) hW
  exact ⟨a, c, hc, InfinityChart.quadraticClosedTuple_isFinite k R g d I hg c hZ,
    relativeCoordinateHom_finite k R d _ ((IsFinite.SpecMap_iff _).mp hf), he, hs⟩

end QuadraticIncidence
