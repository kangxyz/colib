/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FiniteCoordinates
public import Colib.AlgebraicGeometry.Normalization.Compactification.NonemptyBoundary
public import Colib.RingTheory.TensorProduct.QuotientCoordinateComparison

/-!
# A normal proper curve from the actual finite separable stage

The original descended quadratic rows give the finite projective-line compactification.
Its actual infinity pullback is retained, and the full complement of the distinct whole-fiber
smooth open becomes finite on a principal base neighborhood. The original bad scheme is
literally the tensor product with B/I, with its actual quotient-induced map. The native
quotient comparison identifies that map with the extended-ideal quotient map.

The near-mark etale chart is not substituted for the whole-fiber open. It proves surjectivity
of the finite projective-line cover and its actual infinity pullback. No infinite-field
hypothesis on the finite stage or transfer presheaf over that stage is introduced.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial IntermediateField
open AlgebraicGeometry.Scheme.RelativeCurve

universe u

namespace QuadraticIncidence.InfinityChart

/-- The actual tensor quotient morphism preserves every original tail coordinate. -/
theorem quadraticCoordinateHom_tensorQuotient
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
    (g : σ → B) (d : ℕ) (I : Ideal B) (c : Fin d × Exponent σ → E) :
    (Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom.comp
      (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c) =
    quadraticCoordinateHom E (E ⊗[K] (B ⧸ I))
      (fun j => (1 : E) ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c := by
  have hmap : MvPolynomial.map (σ := Fin d) (RingHom.id E) = RingHom.id _ :=
    RingHom.ext MvPolynomial.map_id
  simpa [hmap] using quadraticCoordinateHom_scalarExtension E E
    (E ⊗[K] B) (E ⊗[K] (B ⧸ I))
    (Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I))
    (fun j => (1 : E) ⊗ₜ[K] g j) d c

/-- The native tensor-quotient equivalence identifies the original bad-scheme coordinates
with the quotient of the unchanged ambient coordinates by the extended ideal. -/
theorem tensorQuotientEquiv_quadraticCoordinateHom
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
    (g : σ → B) (d : ℕ) (I : Ideal B) (c : Fin d × Exponent σ → E) :
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) E B E I).toRingHom.comp
      (quadraticCoordinateHom E (E ⊗[K] (B ⧸ I))
        (fun j => (1 : E) ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c) =
    (Ideal.Quotient.mk (I.map (Algebra.TensorProduct.includeRight (R := K) (A := E)))).comp
      (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c) := by
  rw [← quadraticCoordinateHom_tensorQuotient, ← RingHom.comp_assoc,
    Algebra.TensorProduct.tensorQuotientEquiv_comp_map_quotient]

/-- The explicit good-neighborhood output on the original tensor-stage scheme and maps.
This is only a name for the displayed geometric conclusions; the following theorem constructs
all its witnesses from finite coordinates, rather than assuming such witnesses. -/
def HasTensorGoodQuadraticNeighborhood
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
    (g : σ → B) (d : ℕ) (I : Ideal B)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (P : Spec (.of (E ⊗[K] B))) (r : E ⊗[K] B) : Prop :=
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
        PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ W

/-- The unchanged tensor-stage coordinates construct a normal proper curve, retaining its
actual bad closed scheme, both opens, the full infinity pullback and the full retained boundary. -/
theorem exists_tensor_good_quadratic_neighborhood
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
    HasTensorGoodQuadraticNeighborhood K E B g d I a c P r := by
  dsimp only [HasTensorGoodQuadraticNeighborhood]
  have hbase := quadraticRelativeCoordinateHom_comp_C E (E ⊗[K] B)
    (fun j => (1 : E) ⊗ₜ[K] g j) d a c
  have hfinite : (quadraticRelativeCoordinateHom E (E ⊗[K] B)
      (fun j => (1 : E) ⊗ₜ[K] g j) d a c).Finite :=
    relativeCoordinateHom_finite E (E ⊗[K] B) d _ hf
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (.of (E ⊗[K] B)))
      (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen (R := .of (E ⊗[K] B)) r
  have : SmoothOfRelativeDimension 1
      (Scheme.Opens.ι (X := Spec (.of (E ⊗[K] B))) (PrimeSpectrum.basicOpen r) ≫
        Spec.map (CommRingCat.ofHom ((quadraticRelativeCoordinateHom E (E ⊗[K] B)
          (fun j => (1 : E) ⊗ₜ[K] g j) d a c).comp Polynomial.C))) := by
    rw [hbase]
    exact hrel
  have hz : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _
      (Algebra.TensorProduct.map_quotient_surjective K E B I)
  have hzf : IsFinite (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((quadraticRelativeCoordinateHom E (E ⊗[K] B)
        (fun j => (1 : E) ⊗ₜ[K] g j) d a c).comp Polynomial.C))) := by
    rw [hbase, ← Spec.map_comp]
    change IsFinite (Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom.comp
        (quadraticCoordinateHom E (E ⊗[K] B) (fun j => (1 : E) ⊗ₜ[K] g j) d c))))
    rw [quadraticCoordinateHom_tensorQuotient]
    exact (IsFinite.SpecMap_iff _).mpr hZ
  obtain ⟨N, D, i, π, b, e, t, hi, hN, hn, hnormal, hπ, hp, hb, hfinite', hpb,
      hrange, hfac, hbase', ht, ha, hsm, hnew, ha', hz'⟩ :=
    exists_good_neighborhood_of_finite_polynomial_coordinates E (MvPolynomial (Fin d) E)
      (E ⊗[K] B) (quadraticRelativeCoordinateHom E (E ⊗[K] B)
        (fun j => (1 : E) ⊗ₜ[K] g j) d a c) hfinite (PrimeSpectrum.basicOpen r)
      (Spec.map (CommRingCat.ofHom ((quadraticRelativeCoordinateHom E (E ⊗[K] B)
        (fun j => (1 : E) ⊗ₜ[K] g j) d a c).comp Polynomial.C)) P)
      (by
        intro Q hQ
        change r ∉ Q.asIdeal
        apply hW Q
        simpa only [hbase] using hQ)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom))
  have := hπ
  have hsurj : Surjective π := by
    apply Scheme.surjective_projectiveLine_cover_of_etale_away (MvPolynomial (Fin d) E)
      (E ⊗[K] B) (quadraticRelativeCoordinateHom E (E ⊗[K] B)
        (fun j => (1 : E) ⊗ₜ[K] g j) d a c)
      rₑ (fun hzero => hrₑ (hzero ▸ P.asIdeal.zero_mem)) _ i π hfac
    exact relativeCoordinateHom_etale_away E (E ⊗[K] B) d _ rₑ he
  have := hsurj
  have hesurj : Surjective e := Scheme.surjective_infinity_pullback _ π b e hpb
  exact ⟨hz, hzf, N, D, i, π, b, e, t, hi, hN, hn, hnormal, hπ, hsurj, hp, hb,
    hfinite', hpb, hesurj, hrange, hfac, hbase', ht, ha, hsm, hnew, ha', hz'⟩

/-- One finite separable stage constructs the normal proper curve from the same descended
parameters, retaining the original marking, both distinct principal opens and the original
bad closed scheme, with surjective native projective-line cover and infinity pullback. -/
theorem exists_finsetSubfield_sameTuple_good_neighborhood
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
        HasTensorGoodQuadraticNeighborhood K E B g d I a' c' P' r' := by
  obtain ⟨t, ht, hfinite, hsep, a', c', rₑ', r', ha, hc, hₑ, hr,
      hdomain, hf', hrₑ', he', hrel', hW', hZ'⟩ :=
    exists_finsetSubfield_sameTuple_geometry K L B g d I s a c P rₑ r hrₑ hf he hrel hW hZ
  have := hdomain
  have hgood : HasTensorGoodQuadraticNeighborhood K (adjoin K (t : Set L)) B g d I a' c'
      (Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) P) r' := by
    apply exists_tensor_good_quadratic_neighborhood K (adjoin K (t : Set L)) B
      g d I a' c' _ rₑ' r'
    · exact hrₑ'
    · exact hf'
    · exact he'
    · exact hrel'
    · exact hW'
    · exact hZ'
  exact ⟨t, ht, hfinite, hsep, a', c', rₑ', r', ha, hc, hₑ, hr,
    hdomain, hf', hrₑ', he', hrel', hW', hZ', hgood⟩

end QuadraticIncidence.InfinityChart
