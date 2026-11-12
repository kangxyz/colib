/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.FiniteStageDescent
public import Colib.AlgebraicGeometry.Morphisms.Smooth.ScalarExtensionCoordinates
public import Colib.AlgebraicGeometry.Limits.ScalarExtensionCoordinateFibers

/-!
# Actual finite-stage marked relative-curve coordinates

One finite separable stage retains the original quadratic coefficients, the etale-near-point
open and the separate smooth whole-fiber open. The original marked point is pushed down by
the actual tensor inclusion. Domain, full-coordinate finiteness and etaleness, relative
dimension one, and whole-fiber containment hold on the original stage objects. The bad closed
scheme remains the actual scalar extension of the original quotient B/I and its same tail
coordinate map is finite. No new parameter tuple or transfer presheaf is introduced.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry MvPolynomial IntermediateField
universe u
namespace QuadraticIncidence.InfinityChart
/-- One actual finite separable stage retains the unchanged marked curve geometry and the
original tensor-stage bad closed subscheme, with the two principal opens kept distinct. -/
theorem exists_finsetSubfield_sameTuple_geometry
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] [IsDomain (L ⊗[K] B)]
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
          (fun j => 1 ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d c').Finite := by
  have hspec := (smoothOfRelativeDimension_basicOpen_iff _ _ _ r 1).mp hrel
  have hs : ((algebraMap (L ⊗[K] B) (Localization.Away r)).comp
      (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom
      ((algebraMap (L ⊗[K] B) (Localization.Away r)).comp
        (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)))).mp
      (@SmoothOfRelativeDimension.smooth 1 _ _ _ hspec)
  obtain ⟨t, ht, hfinite, hsep, a', c', rₑ', r', ha, hc, hₑ, hr, hf', he', -⟩ :=
    exists_finsetSubfield_sameTuple_coordinates K L B g d s a c rₑ r hf he hs
  subst rₑ r
  have hi : Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom K (adjoin K (t : Set L)) L) (AlgHom.id K B) =
      finsetTensorInclusion K L B t := rfl
  have hcL (q : Fin d × Exponent σ) :
      algebraMap (adjoin K (t : Set L)) L (c' q) = c q := hc q
  refine ⟨t, ht, hfinite, hsep, a', c', rₑ', r', ha, hc, rfl, rfl, ?_, hf', hrₑ, he', ?_, ?_, ?_⟩
  · exact Function.Injective.isDomain (finsetTensorInclusion K L B t).toRingHom
      (finsetTensorInclusion_injective K L B t)
  · apply smoothOfRelativeDimension_basicOpen_of_scalarTower K (adjoin K (t : Set L)) L B
      (fun i : Fin d => aeval (fun j => (1 : adjoin K (t : Set L)) ⊗ₜ[K] g j)
        (parameterTuple (adjoin K (t : Set L)) σ d c' i).val) r' 1
    change SmoothOfRelativeDimension 1
      ((Scheme.Opens.ι (X := Spec (.of (L ⊗[K] B)))
        (PrimeSpectrum.basicOpen (finsetTensorInclusion K L B t r'))) ≫ _)
    simpa only [quadraticCoordinateHom, originalFunction_tensorInclusion, hcL, ← hi,
      Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.id_apply] using hrel
  · apply fiber_subset_basicOpen_of_aeval_scalarTower K (adjoin K (t : Set L)) L B
      (fun i : Fin d => aeval (fun j => (1 : adjoin K (t : Set L)) ⊗ₜ[K] g j)
        (parameterTuple (adjoin K (t : Set L)) σ d c' i).val) P r'
    simpa only [quadraticCoordinateHom, originalFunction_tensorInclusion, hcL, ← hi,
      Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.id_apply] using hW
  · apply of_quadraticCoordinateHom_scalarTower K (adjoin K (t : Set L)) L (B ⧸ I)
      (fun j => 1 ⊗ₜ[K] Ideal.Quotient.mk I (g j)) d _
      RingHom.Finite.codescendsAlong_faithfullyFlat RingHom.finite_respectsIso c'
    simpa only [hcL, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using hZ
end QuadraticIncidence.InfinityChart
