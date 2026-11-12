/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Limits.FiniteSubfieldRationalMarking
import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStagePresentation

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry MvPolynomial IntermediateField
open QuadraticIncidence QuadraticIncidence.InfinityChart

universe u

noncomputable section

/-- Full finite-subfield interface, including every later enlargement and exact marking. -/
example
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {Y : Scheme.{u}} (η : Y ⟶ Spec (.of L)) (x : Y ⟶ Spec (.of (L ⊗[K] B)))
    (hx₁ : x ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) = η)
    (hx₂ : x ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := B)).toRingHom) = η ≫ ξ)
    (s : Finset L) :
    ∃ s₀ : Finset L, s ⊆ s₀ ∧ ∀ (t : Finset L), s₀ ⊆ t →
      ∃ xE : Spec (.of (adjoin K (t : Set L))) ⟶
          Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)),
        xE ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B))) = 𝟙 _ ∧
        η ≫ Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) ≫ xE =
          x ≫ Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) ∧
        ∀ y : Y, xE default =
          Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) (x y) :=
  Scheme.exists_finsetSubfield_rationalTensorMarking K L B ξ hξ η x hx₁ hx₂ s

/-- The frozen good-neighborhood producer retains every conclusion at the exact rational mark. -/
example
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] [Algebra.Smooth K B] [IsDomain (L ⊗[K] B)]
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ Spec (.of L))
    (x : Spec (.of Ω) ⟶ Spec (.of (L ⊗[K] B)))
    (hx₁ : x ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) = η)
    (hx₂ : x ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := B)).toRingHom) = η ≫ ξ)
    (s : Finset L) (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (rₑ r : L ⊗[K] B) (hrₑ : rₑ ∉ (x default).asIdeal)
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
        (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)) (x default) →
      Q ∈ PrimeSpectrum.basicOpen r)
    (hZ : (quadraticCoordinateHom L (L ⊗[K] (B ⧸ I))
      (fun j => (1 : L) ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c).Finite) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      Algebra.IsSeparable K (adjoin K (t : Set L)) ∧
      ∃ (a' : Exponent σ → adjoin K (t : Set L))
        (c' : Fin d × Exponent σ → adjoin K (t : Set L))
        (rₑ' r' : (adjoin K (t : Set L)) ⊗[K] B),
        (∀ e, (a' e : L) = a e) ∧ (∀ q, (c' q : L) = c q) ∧
        finsetTensorInclusion K L B t rₑ' = rₑ ∧ finsetTensorInclusion K L B t r' = r ∧
        let E : Type u := adjoin K (t : Set L)
        let g' : σ → E ⊗[K] B := fun j => 1 ⊗ₜ[K] g j
        let f := quadraticCoordinateHom E (E ⊗[K] B) g' d c'
        let P' : Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)) :=
          Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) (x default)
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
        ∃ xE : Spec (.of E) ⟶ Spec (.of (E ⊗[K] B)),
          xE ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] B))) = 𝟙 _ ∧
          η ≫ Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) ≫ xE =
            x ≫ Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) ∧
          xE default = P' := by
  obtain ⟨s₀, hs₀, hpoint⟩ :=
    Scheme.exists_finsetSubfield_rationalTensorMarking K L B ξ hξ η x hx₁ hx₂ s
  obtain ⟨t, ht, hfinite, hsep, a', c', rₑ', r', ha, hc, hₑ, hr,
      hdomain, hf', hrₑ', he', hrel', hW', hZ', hgood⟩ :=
    exists_finsetSubfield_sameTuple_good_neighborhood K L B g d I s₀ a c
      (x default) rₑ r hrₑ hf he hrel hW hZ
  obtain ⟨xE, hsection, hmark, himage⟩ := hpoint t ht
  exact ⟨t, hs₀.trans ht, hfinite, hsep, a', c', rₑ', r', ha, hc, hₑ, hr,
    hdomain, hf', hrₑ', he', hrel', hW', hZ', hgood, xE, hsection, hmark, himage default⟩

end
