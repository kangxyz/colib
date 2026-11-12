/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FinitePolynomialProducer
public import Colib.AlgebraicGeometry.Morphisms.Smooth.Bertini.WholeFiberPrincipalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-! # Actual presentations from finite algebra coordinates and pointwise whole-fiber smoothness

The affine neighborhood, normality, compactification and retained presentation are
all constructed. The remaining algebra input is exactly a finite augmented
polynomial coordinate with the original tail, its finite fixed bad quotient,
and actual smoothness at every point of the selected projection fiber.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The native geometric producer with no supplied affine neighborhood or
compactification. The field is arbitrary, and I and J need not be radical. -/
theorem nonempty_originalEtalePresentation_of_finite_algebra_coordinates
    (k R B : Type u) [Field k] [CommRing R] [CommRing B] [IsDomain B]
    [Algebra k R] [Algebra k B] [Algebra.Smooth k R] [Algebra.Smooth k B]
    (φ : R →ₐ[k] B) (ψ : Polynomial R →+* B)
    (hψ : ψ.comp Polynomial.C = φ.toRingHom)
    [IsFinite (Spec.map (CommRingCat.ofHom ψ))]
    (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    (hsm : ∀ Q : PrimeSpectrum B,
      Ideal.comap φ.toRingHom P.asIdeal = Ideal.comap φ.toRingHom Q.asIdeal →
      ∃ b ∉ Q.asIdeal, SmoothOfRelativeDimension 1
        (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away b)).comp φ.toRingHom))))
    (I J : Ideal B) (hIJ : I ≤ J)
    [IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom))]
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a) (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ)
    [IsFinite (p ∣_ U)] :
    Nonempty (OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s P) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hr : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have hB : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : IsNormal (Spec (.of B)) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field
      (Spec.map (CommRingCat.ofHom (algebraMap k B))))
  have hproj : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (ψ.comp Polynomial.C)) = _
    rw [hψ]
  obtain ⟨b, _, hb, hbs⟩ :=
    QuadraticIncidence.exists_closedFiber_principal_smooth k R B φ P 1 hsm
  let V : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen b
  have : IsAffine V.toScheme := IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of B) b).hom
  have : SmoothOfRelativeDimension 1
      (V.ι ≫ Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
    rw [hproj]
    exact hbs
  have hwhole : ∀ x : Spec (.of B),
      (Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) x =
        (Spec.map (CommRingCat.ofHom ψ) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) P →
      x ∈ V := by
    intro x hx
    rw [hproj] at hx
    apply hb x
    exact (congrArg PrimeSpectrum.asIdeal hx).symm
  have : IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
    rw [hproj]
    infer_instance
  have hfield : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x
  have hout := nonempty_originalEtalePresentation_of_finite_polynomial_coordinates
    k R B (Spec.map (CommRingCat.ofHom (algebraMap k R))) (Spec.map (CommRingCat.ofHom ψ))
      P V hwhole I J hIJ p a s hs H ha hcover U hU
  simpa only [← Category.assoc, hproj, hfield] using hout

end AlgebraicGeometry.Scheme.RelativeCurve
