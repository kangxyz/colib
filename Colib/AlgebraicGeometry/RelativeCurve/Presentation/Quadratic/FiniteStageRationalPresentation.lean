/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStagePresentation
public import Colib.AlgebraicGeometry.Limits.FiniteSubfieldRationalMarking
public import Colib.AlgebraicGeometry.Polynomial.RationalCoordinateSection

/-! # One actual finite stage carries the original tuple and rational marking

The rational-point producer first fixes s₀. The existing geometric producer enlarges
that exact finite set, and its chosen t is then reused, not reselected.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial IntermediateField
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- The original rational mark and the original quadratic tuple coexist on the same
finite separable tensor stage, with the actual compactification and both opens unchanged. -/
theorem exists_finsetSubfield_sameTuple_rational_good_neighborhood
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] [Algebra.Smooth K B] [IsDomain (L ⊗[K] B)]
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (s : Finset L) (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (rₑ r : L ⊗[K] B)
    (hrₑ : rₑ ∉ (Scheme.rationalTensorPoint K L B ξ hξ default).asIdeal)
    (hf : (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j)
      (d + 1) (prependParameters L d a c)).Finite)
    (he : ((algebraMap (L ⊗[K] B) (Localization.Away rₑ)).comp
      (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j)
        (d + 1) (prependParameters L d a c))).Etale)
    (hrel : SmoothOfRelativeDimension 1
      ((Scheme.Opens.ι (X := Spec (.of (L ⊗[K] B))) (PrimeSpectrum.basicOpen r)) ≫
        Spec.map (CommRingCat.ofHom
          (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c))))
    (hW : ∀ Q : Spec (.of (L ⊗[K] B)),
      Spec.map (CommRingCat.ofHom
        (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)) Q =
      Spec.map (CommRingCat.ofHom
        (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c))
          (Scheme.rationalTensorPoint K L B ξ hξ default) →
      Q ∈ PrimeSpectrum.basicOpen r)
    (hZ : (quadraticCoordinateHom L (L ⊗[K] (B ⧸ I))
      (fun j => (1 : L) ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c).Finite) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      Algebra.IsSeparable K (adjoin K (t : Set L)) ∧
      ∃ (xE : Spec (.of (adjoin K (t : Set L))) ⟶
          Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)))
        (ε : ((adjoin K (t : Set L)) ⊗[K] B) →ₐ[adjoin K (t : Set L)]
          (adjoin K (t : Set L)))
        (a' : Exponent σ → adjoin K (t : Set L))
        (c' : Fin d × Exponent σ → adjoin K (t : Set L))
        (rₑ' r' : (adjoin K (t : Set L)) ⊗[K] B),
        (∀ e, (a' e : L) = a e) ∧ (∀ q, (c' q : L) = c q) ∧
        finsetTensorInclusion K L B t rₑ' = rₑ ∧ finsetTensorInclusion K L B t r' = r ∧
        let E : Type u := adjoin K (t : Set L)
        let g' : σ → E ⊗[K] B := fun j => 1 ⊗ₜ[K] g j
        let f := quadraticCoordinateHom E (E ⊗[K] B) g' d c'
        let P' : Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)) :=
          Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom)
            (Scheme.rationalTensorPoint K L B ξ hξ default)
        IsDomain (E ⊗[K] B) ∧
        (quadraticCoordinateHom E (E ⊗[K] B) g' (d + 1)
          (prependParameters E d a' c')).Finite ∧
        rₑ' ∉ P'.asIdeal ∧
        ((algebraMap (E ⊗[K] B) (Localization.Away rₑ')).comp
          (quadraticCoordinateHom E (E ⊗[K] B) g' (d + 1)
            (prependParameters E d a' c'))).Etale ∧
        SmoothOfRelativeDimension 1
          ((Scheme.Opens.ι (X := Spec (.of (E ⊗[K] B))) (PrimeSpectrum.basicOpen r')) ≫
            Spec.map (CommRingCat.ofHom f)) ∧
        (∀ Q : Spec (.of (E ⊗[K] B)), Spec.map (CommRingCat.ofHom f) Q =
          Spec.map (CommRingCat.ofHom f) P' → Q ∈ PrimeSpectrum.basicOpen r') ∧
        (quadraticCoordinateHom E (E ⊗[K] (B ⧸ I))
          (fun j => 1 ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c').Finite ∧
        HasTensorGoodQuadraticNeighborhood K E B g d I a' c' P' r' ∧
        xE ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] B))) = 𝟙 _ ∧
        Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) ≫ xE =
          Scheme.rationalTensorPoint K L B ξ hξ ≫
            Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) ∧
        xE default = P' ∧
        Spec.map (CommRingCat.ofHom ε.toRingHom) = xE := by
  let x := Scheme.rationalTensorPoint K L B ξ hξ
  obtain ⟨s₀, hs₀, hrational⟩ :=
    Scheme.exists_finsetSubfield_rationalTensorMarking K L B ξ hξ (𝟙 _) x
      (by simp [x])
      (by simpa [x] using Scheme.rationalTensorPoint_snd K L B ξ hξ) s
  obtain ⟨t, ht, hfin, hsep, a', c', rₑ', r', ha, hc, hₑ, hr,
      hdomain, hf', hrₑ', he', hrel', hW', hZ', hgood⟩ :=
    exists_finsetSubfield_sameTuple_good_neighborhood K L B g d I s₀ a c
      (x default) rₑ r hrₑ hf he hrel hW hZ
  obtain ⟨xE, hxE, hmark, hpoint⟩ := hrational t ht
  obtain ⟨ε, hε⟩ := Scheme.exists_algHom_of_rational_schemePoint xE hxE
  refine ⟨t, hs₀.trans ht, hfin, hsep, xE, ε, a', c', rₑ', r', ha, hc, hₑ, hr,
    hdomain, hf', hrₑ', he', hrel', hW', hZ', hgood, hxE, ?_, hpoint default, hε⟩
  · simpa only [Category.id_comp] using hmark

end QuadraticIncidence.InfinityChart
