/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.Open.PolynomialBaseChange
public import Colib.AlgebraicGeometry.Scheme.AffinePullbackSections
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # The complement of a finite mark meets every affine-line fiber -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite mark in the polynomial line misses the generic point of every
fiber. The integral equation of the original coordinate provides a monic
equation on the entire mark, including any nilpotents. -/
theorem surjective_puncture_polynomialProjection_of_finite_mark
    (R : Type u) [CommRing R] {A Z : Scheme.{u}}
    (a : A ⟶ Spec (.of R[X])) (z : Z ⟶ Spec (.of R[X]))
    [IsFinite (z ≫ polynomialProjection (.of R))]
    (hcover : ∀ x : Spec (.of R[X]), x ∈ Set.range a ∨ x ∈ Set.range z) :
    Function.Surjective (a ≫ polynomialProjection (.of R)) := by
  let B := Γ(Z, ⊤)
  let φ : R[X] →+* B := specSectionsMap z
  let : Algebra R B := (φ.comp C).toAlgebra
  let : IsAffine Z := isAffine_of_isAffineHom (z ≫ polynomialProjection (.of R))
  let : Module.Finite R B := by
    apply RingHom.finite_algebraMap.mp
    apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (φ.comp C))).mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Spec_map_specSectionsMap z]
    rw [Category.assoc]
    change IsFinite (Z.isoSpec.inv ≫ z ≫ polynomialProjection (.of R))
    infer_instance
  have hi : _root_.IsIntegral R (φ X) := Algebra.IsIntegral.isIntegral (φ X)
  obtain ⟨m, hm, hme⟩ := hi
  have hφ : (aeval (φ X) : R[X] →ₐ[R] B).toRingHom = φ := by
    apply Polynomial.ringHom_ext
    · intro r
      exact aeval_C _ _
    · exact aeval_X _
  have hmφ : φ m = 0 := by
    exact (congrArg (fun f : R[X] →+* B ↦ f m) hφ).symm.trans hme
  intro y
  let ψ := Polynomial.mapRingHom (algebraMap R y.asIdeal.ResidueField)
  let η : PrimeSpectrum (Polynomial y.asIdeal.ResidueField) := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum R[X] := PrimeSpectrum.comap ψ η
  have hw : polynomialProjection (.of R) w = y := by
    apply PrimeSpectrum.ext
    ext r
    change Polynomial.map (algebraMap R y.asIdeal.ResidueField) (C r) ∈
      (⊥ : Ideal (Polynomial y.asIdeal.ResidueField)) ↔ r ∈ y.asIdeal
    rw [Polynomial.map_C, Ideal.mem_bot, C_eq_zero]
    exact SetLike.ext_iff.mp (Ideal.ker_algebraMap_residueField y.asIdeal) r
  have hmw : m ∉ w.asIdeal := by
    change Polynomial.map (algebraMap R y.asIdeal.ResidueField) m ∉
      (⊥ : Ideal (Polynomial y.asIdeal.ResidueField))
    rw [Ideal.mem_bot]
    exact (hm.map (algebraMap R y.asIdeal.ResidueField)).ne_zero
  have hz : w ∉ Set.range z := by
    rintro ⟨x, hx⟩
    let x' := Z.isoSpec.hom x
    have he : Spec.map (CommRingCat.ofHom φ) x' = w := by
      rw [Spec_map_specSectionsMap z]
      change (Z.isoSpec.hom ≫ Z.isoSpec.inv ≫ z) x = w
      simpa only [Iso.hom_inv_id_assoc] using hx
    apply hmw
    rw [← he]
    change φ m ∈ x'.asIdeal
    rw [hmφ]
    exact x'.asIdeal.zero_mem
  obtain ⟨x, hx⟩ := (hcover w).resolve_right hz
  exact ⟨x, (congrArg (polynomialProjection (.of R)) hx).trans hw⟩

end AlgebraicGeometry.Scheme
