/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageRationalPresentation
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteSeparableRetainedEtaleSmoothSite
public import Colib.RingTheory.Bertini.RelativePolynomialCoordinateAlgebra

/-! # The same finite stage, tuple, opens and rational mark in the original smooth site -/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial IntermediateField
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- Native chart data for the literal relative polynomial map over Spec K.
Finiteness and separability are supplied proofs for this same E, not new choices. -/
def HasQuadraticRetainedNativeChart
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra E B]
    (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E)
    (d : ℕ) (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B)) (re r : B) : Prop := by
  letI := hfin
  letI := hsep
  exact
    let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
    let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
    let q := pullback.fst je jr ≫ je ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    let p := Spec.map (CommRingCat.ofHom
      (Polynomial.C : MvPolynomial (Fin d) E →+* Polynomial (MvPolynomial (Fin d) E)))
    ∃ (hq : Etale q) (hp : Smooth p)
      (s : Spec (.of (MvPolynomial (Fin d) E)) ⟶
        Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) (hs : s ≫ p = 𝟙 _)
      (η : Spec (.of E) ⟶ Spec (.of (MvPolynomial (Fin d) E)))
      (ξ : Spec (.of E) ⟶ Scheme.quadraticRetainedEtaleChart re r),
      let Y := Scheme.SmoothSite.mk
        (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))
      let hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin d) E))))
      let hA : IsAffine (Scheme.quadraticRetainedEtaleChart re r) :=
        Scheme.quadraticRetainedEtaleChart_isAffine re r
      let hZ : IsAffine (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) := inferInstance
      let qs := @Scheme.SmoothSite.EtaleChart.chart (Spec (.of K)) Y hY
        (Scheme.quadraticRetainedEtaleChart re r) (Spec (.of (Polynomial (MvPolynomial (Fin d) E))))
        hA hZ p hp q hq
      let ps := @Scheme.SmoothSite.EtaleChart.projection (Spec (.of K)) Y hY
        (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) hZ p hp
      let ss := @Scheme.SmoothSite.EtaleChart.sectionMap (Spec (.of K)) Y hY
        (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) hZ p hp s hs
      ss ≫ ps = 𝟙 Y ∧ ξ ≫ qs.left = η ≫ ss.left ∧
        ξ ≫ pullback.snd je jr ≫ jr = x

/-- Construct the named native-chart proposition before entering any finite-stage
existential. This confines the native category definitional equality to a small leaf. -/
theorem hasQuadraticRetainedNativeChart_of_rational_mark
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra E B]
    (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E)
    (d : ℕ) (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] B)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _)
    (re r : B) (hre : re ∉ (x default).asIdeal) (hr : r ∉ (x default).asIdeal)
    (he : ((algebraMap B (Localization.Away re)).comp f.toRingHom).Etale) :
    HasQuadraticRetainedNativeChart K E B hfin hsep d f x re r := by
  let : Module.Finite K E := hfin
  let : Algebra.IsSeparable K E := hsep
  exact Scheme.exists_finiteSeparable_quadraticRetainedEtaleChart_smoothSite K E d
    f x hx re r hre hr he

/-- The original full tuple, whole-fiber open and point recovery supply the marked
relative chart without asking for either open-membership hypothesis again. -/
theorem hasQuadraticRetainedNativeChart_of_pointed_tuple
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra E B]
    (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E)
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _)
    (P : Spec (.of B)) (hpoint : x default = P) (re r : B)
    (hre : re ∉ P.asIdeal)
    (he : ((algebraMap B (Localization.Away re)).comp
      (quadraticCoordinateHom E B g (d + 1) (prependParameters E d a c))).Etale)
    (hW : ∀ Q : Spec (.of B),
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom E B g d c)) Q =
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom E B g d c)) P →
      Q ∈ PrimeSpectrum.basicOpen r) :
    HasQuadraticRetainedNativeChart K E B hfin hsep d
      (relativeCoordinateAlgHom E B d
        (fun i => aeval g (parameterTuple E σ (d + 1)
          (prependParameters E d a c) i).val)) x re r := by
  have hreMark : re ∉ (x default).asIdeal := by
    rw [hpoint]
    exact hre
  have hrMark : r ∉ (x default).asIdeal := by
    rw [hpoint]
    exact hW P rfl
  apply hasQuadraticRetainedNativeChart_of_rational_mark K E B hfin hsep d
    _ x hx re r hreMark hrMark
  exact relativeCoordinateHom_etale_away E B d _ re he

/-- One invocation preserves all geometric output and adds its native chart. -/
theorem exists_finsetSubfield_sameTuple_rational_native_chart
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
        Spec.map (CommRingCat.ofHom ε.toRingHom) = xE ∧
        ∃ (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E),
          HasQuadraticRetainedNativeChart K E (E ⊗[K] B) hfin hsep d
            (relativeCoordinateAlgHom E (E ⊗[K] B) d
              (fun i => aeval g' (parameterTuple E σ (d + 1)
                (prependParameters E d a' c') i).val)) xE rₑ' r'  := by
  obtain ⟨t, ht, hfin, hsep, xE, ε, a', c', re', r', ha, hc, hre, hr,
      hdomain, hf', hrep, he', hrel', hW', hZ', hgood, hxE, hmark, hpoint, hε⟩ :=
    exists_finsetSubfield_sameTuple_rational_good_neighborhood K L B g d I s a c
      ξ hξ rₑ r hrₑ hf he hrel hW hZ
  refine ⟨t, ht, hfin, hsep, xE, ε, a', c', re', r', ha, hc, hre, hr,
    hdomain, hf', hrep, he', hrel', hW', hZ', hgood, hxE, hmark, hpoint, hε,
    hfin, hsep, ?_⟩
  exact hasQuadraticRetainedNativeChart_of_pointed_tuple K
    (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B) hfin hsep
    (fun j => (1 : adjoin K (t : Set L)) ⊗ₜ[K] g j) d a' c' xE hxE
    _ hpoint re' r' hrep he' hW'

end QuadraticIncidence.InfinityChart
