/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStagePresentation

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial IntermediateField
open AlgebraicGeometry.Scheme.RelativeCurve QuadraticIncidence QuadraticIncidence.InfinityChart

universe u

/-- The complete same-stage producer needs no infinite-field or rational-mark assumption. -/
example
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] [Algebra.Smooth K B] [IsDomain (L ⊗[K] B)]
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (s : Finset L) (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (P : Spec (.of (L ⊗[K] B))) (rₑ r : L ⊗[K] B) (hrₑ : rₑ ∉ P.asIdeal)
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
        (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)) P →
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
          Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) P
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
        HasTensorGoodQuadraticNeighborhood K E B g d I a' c' P' r' :=
  exists_finsetSubfield_sameTuple_good_neighborhood K L B g d I s a c P rₑ r hrₑ hf he hrel hW hZ

/-- Unfolding the output gives the actual maps and all geometric conclusions. -/
example
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] [Algebra.Smooth K B] [IsDomain (E ⊗[K] B)]
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P : Spec (.of (E ⊗[K] B))) (rₑ r : E ⊗[K] B) (hrₑ : rₑ ∉ P.asIdeal)
    (hf : (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j)
      (d + 1) (prependParameters E d a c)).Finite)
    (he : ((algebraMap (E ⊗[K] B) (Localization.Away rₑ)).comp
      (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j)
        (d + 1) (prependParameters E d a c))).Etale)
    (hrel : SmoothOfRelativeDimension 1
      ((Scheme.Opens.ι (X := Spec (.of (E ⊗[K] B))) (PrimeSpectrum.basicOpen r)) ≫
        Spec.map (CommRingCat.ofHom
          (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c))))
    (hW : ∀ Q : Spec (.of (E ⊗[K] B)),
      Spec.map (CommRingCat.ofHom
        (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c)) Q =
      Spec.map (CommRingCat.ofHom
        (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c)) P →
      Q ∈ PrimeSpectrum.basicOpen r)
    (hZ : (quadraticCoordinateHom E (E ⊗[K] (B ⧸ I))
      (fun j => (1 : E) ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c).Finite) :
    let R := MvPolynomial (Fin d) E
    let f := quadraticRelativeCoordinateHom E (E ⊗[K] B)
      (fun j => (1 : E) ⊗ₜ[K] g j) d a c
    let W : (Spec (.of (E ⊗[K] B))).Opens := PrimeSpectrum.basicOpen r
    let s := Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) P
    let Z := Spec (.of (E ⊗[K] (B ⧸ I)))
    let z : Z ⟶ Spec (.of (E ⊗[K] B)) := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom)
    IsClosedImmersion z ∧ IsFinite (z ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C))) ∧
    ∃ (N D : Scheme.{u}) (i : Spec (.of (E ⊗[K] B)) ⟶ N) (π : N ⟶ projectiveLine R)
      (b : D ⟶ N) (e : D ⟶ Spec (.of R)) (t : R) (hi : IsOpenImmersion i),
      letI := hi;
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsFinite π ∧ Surjective π ∧ IsProper (π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsClosedImmersion b ∧ IsFinite (b ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsPullback b e π (projectiveLineInfinitySection R) ∧ Surjective e ∧
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
        PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ W :=
  exists_tensor_good_quadratic_neighborhood K E B g d I a c P rₑ r hrₑ hf he hrel hW hZ

/-- The original bad scheme retains the native quotient-coordinate comparison. -/
example (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
    (g : σ → B) (d : ℕ) (I : Ideal B) (c : Fin d × Exponent σ → E) :
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) E B E I).toRingHom.comp
      (quadraticCoordinateHom E (E ⊗[K] (B ⧸ I))
        (fun j => (1 : E) ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c) =
    (Ideal.Quotient.mk (I.map (Algebra.TensorProduct.includeRight (R := K) (A := E)))).comp
      (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c) :=
  tensorQuotientEquiv_quadraticCoordinateHom K E B g d I c
