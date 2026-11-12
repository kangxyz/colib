/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Bertini.LargePrimeWholeFiberInfinity
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.QuadraticFiniteCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.PolynomialAlgebraProducer
public import Colib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineScalarClosedSquare
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FiniteLocusBadIdeal

/-! # Actual original étale presentations over the same two large prime extensions

The fixed bad ideal is produced from the original étale map before any scalar
choice. Actual scalar infinity avoidance proves both coordinate maps finite;
whole-fiber smoothness feeds the native normalization/retention producer. The
full mapped prescribed quotient and literal pullback maps are never replaced.
The final wrapper constructs the finite generators and residue basis internally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module _root_.MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe u

namespace QuadraticIncidence.InfinityChart

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Actual finite scalar presentations for one original diagram. The generator
family is the original affine family; no basis, bad ideal, finite coordinate,
compactification, presentation or target neighborhood is supplied. -/
theorem exists_two_prime_originalEtalePresentations_of_generators
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k ℓ r)
        let S := B ⊗[k] L
        let ρ := Spec.map (CommRingCat.ofHom (algebraMap B S))
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap B S) y = x ∧
            (∀ z : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap B S) z = x → z = y) ∧
            Nonempty (OriginalEtalePresentation L
              (Spec.map (CommRingCat.ofHom (algebraMap L S)))
              (pullback.snd p ρ) (pullback.snd a ρ)
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S)))))
              (Scheme.quotientBaseChangeEtaleLift B S J p s hs) y) := by
  let := Fintype.ofFinite σ
  obtain ⟨I, hI, hIJ, U, hU, hpU⟩ :=
    exists_fixed_finite_locus_bad_ideal k B p J hJ
  obtain ⟨n, m, hn, hm, hnm, h⟩ :=
    exists_two_prime_wholeFiber_infinity_parameters k B ℓ x I hI g hg d hd
      1 one_ne_zero N₀
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdeg, hdom, y, hy, hyunique, hymax, hgS, a₀, c, _hq, hW, hZ, _he, hsm⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k ℓ r)
  let S := B ⊗[k] L
  let gS := algebraMap B S ∘ g
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap B S))
  let : IsDomain S := hdom
  let : y.asIdeal.IsMaximal := hymax
  let : Algebra.Smooth L S :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing L S
  let R := MvPolynomial (Fin d) L
  let φ : R →ₐ[L] S := aeval (R := L)
    (fun i => aeval gS (parameterTuple L σ d c i).val)
  let ψ := quadraticRelativeCoordinateHom L S gS d a₀ c
  have hψ : ψ.comp Polynomial.C = φ.toRingHom :=
    quadraticRelativeCoordinateHom_comp_C L S gS d a₀ c
  have hψfinite := quadraticRelativeTuple_isFinite L S gS d hgS a₀ c hW
  let : IsFinite (Spec.map (CommRingCat.ofHom ψ)) := by
    dsimp only [ψ]
    exact hψfinite
  let : IsFinite (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.map (algebraMap B S)))) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    rw [← Spec.map_comp]
    exact quadraticClosedTuple_isFinite L S gS d
      (I.map (algebraMap B S)) hgS c hZ
  let : IsFinite (p ∣_ U) := hpU
  obtain ⟨hUS, hpUS⟩ :=
    Scheme.finite_pullback_on_mapped_ideal_complement B S p I U hU
  let : IsFinite ((pullback.snd p ρ) ∣_ ρ ⁻¹ᵁ U) := hpUS
  refine ⟨hdeg, hdom, y, hy, hyunique, ?_⟩
  exact nonempty_originalEtalePresentation_of_finite_algebra_coordinates
    L R S φ ψ hψ y hsm
    (I.map (algebraMap B S)) (J.map (algebraMap B S)) (Ideal.map_mono hIJ)
    (pullback.snd p ρ) (pullback.snd a ρ)
    (Scheme.quotientBaseChangeEtaleLift B S J p s hs)
    (Scheme.quotientBaseChangeEtaleLift_snd B S J p s hs)
    (Scheme.quotientBaseChangeEtaleLift_isPullback B S J p s hs H)
    (Scheme.quotientBaseChange_punctured_disjoint B S J a ha)
    (Scheme.quotientBaseChange_punctured_cover B S J a hcover)
    (ρ ⁻¹ᵁ U) hUS

/-- The two prime scalar presentations are produced from the original smooth
affine domain and complete original étale diagram alone. Finite generators,
residue basis, bad ideal, infinity conditions, finite coordinates, normalization,
whole-fiber neighborhood and every presentation field are constructed internally.
This theorem retains the original maps and full nonreduced prescribed scheme. -/
theorem exists_two_prime_originalEtalePresentations
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥)
    (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k ℓ r)
        let S := B ⊗[k] L
        let ρ := Spec.map (CommRingCat.ofHom (algebraMap B S))
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap B S) y = x ∧
            (∀ z : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap B S) z = x → z = y) ∧
            Nonempty (OriginalEtalePresentation L
              (Spec.map (CommRingCat.ofHom (algebraMap L S)))
              (pullback.snd p ρ) (pullback.snd a ρ)
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S)))))
              (Scheme.quotientBaseChangeEtaleLift B S J p s hs) y) := by
  classical
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := B)
  have hg : Algebra.adjoin k (Set.range (fun t : G => (t : B))) = ⊤ := by
    convert hG using 1
    congr 1
    ext b
    simp
  exact exists_two_prime_originalEtalePresentations_of_generators
    k B ℓ x J hJ (fun t : G => (t : B)) hg d hd p a s hs H ha hcover N₀

end QuadraticIncidence.InfinityChart
