/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousEtaleGoodNeighborhood
import Colib.AlgebraicGeometry.Morphisms.Etale.RationalMarking

open CategoryTheory AlgebraicGeometry MvPolynomial QuadraticIncidence
open QuadraticIncidence.InfinityChart

universe u

noncomputable section

/-- With no prescribed nonempty closed scheme, the unit ideal supplies the required nonzero ideal.
The étale chart and the compactification still retain exactly the same generated tuple. -/
example (k B : Type u) [Field k] [Infinite k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → B) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (d : ℕ) (hd : Algebra.trdeg k B = (d + 1 : ℕ)) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k) (rₑ : B),
      rₑ ∉ P.asIdeal ∧
      Etale (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away rₑ)).comp
        (aeval (R := k) (fun j => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom))) ∧
      ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
        (π : N ⟶ projectiveLine (MvPolynomial (Fin d) k)),
        IsIntegral N ∧ IsOpenImmersion i ∧ IsFinite π ∧ Surjective π ∧
        IsProper (π ≫ (projectiveLine (MvPolynomial (Fin d) k) ↘
          Spec (.of (MvPolynomial (Fin d) k)))) ∧
        i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
          projectiveLineXChart (MvPolynomial (Fin d) k) := by
  obtain ⟨a, c, r, _, _, _, ⟨rₑ, hrₑ, he⟩, N, D, i, π, b, e, t, hi,
    hN, _, _, hπ, hsurj, hp, _, _, _, _, hfac, _⟩ :=
    exists_simultaneous_etale_good_quadratic_neighborhood k B P ⊤ top_ne_bot
      g hg d hd 1 one_ne_zero
  exact ⟨a, c, rₑ, hrₑ, (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he,
    N, i, π, hN, hi, hπ, hsurj, hp, hfac⟩

/-- A mark of the actual same-tuple principal chart descends over its rational image.
This statement does not replace the distinct whole-fiber smooth open by the étale chart. -/
example (k B : Type u) [Field k] [IsSepClosed k] [CommRing B] [Algebra k B]
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k) (rₑ : B)
    (he : ((algebraMap B (Localization.Away rₑ)).comp
      (aeval (R := k) (fun j => aeval g
        (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom).Etale)
    {Ω : Type u} [Field Ω]
    (x : Spec (.of k) ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) k)))
    (cΩ : Spec (.of Ω) ⟶ Spec (.of k))
    (ξ : Spec (.of Ω) ⟶ Spec (.of (Localization.Away rₑ)))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away rₑ)).comp
      (aeval (R := k) (fun j => aeval g
        (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom)) = cΩ ≫ x) :
    ∃ l : Spec (.of k) ⟶ Spec (.of (Localization.Away rₑ)),
      l ≫ Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away rₑ)).comp
        (aeval (R := k) (fun j => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom)) = x ∧
      cΩ ≫ l = ξ := by
  let f := Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away rₑ)).comp
    (aeval (R := k) (fun j => aeval g
      (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom))
  let : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he
  exact Scheme.exists_rational_lift_of_etale_marking f x cΩ ξ hξ

#print axioms exists_simultaneous_etale_good_quadratic_neighborhood

end
