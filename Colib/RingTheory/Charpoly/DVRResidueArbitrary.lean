/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Charpoly.FiniteLength
public import Colib.RingTheory.Charpoly.BasicArbitrary
public import Colib.RingTheory.Charpoly.DVRResidue

/-!
# Actual DVR residue characteristic polynomials over arbitrary fields

The literal closed fibre is compared with the original finite-free algebra by
characteristic-polynomial base change. The native finite-length characteristic
polynomial then retains every nilpotent layer, giving the full ramification power.
No polynomial evaluation argument, infinite residue field or separability is used.

The closed-fibre and residue-coordinate arguments adapt
`Colib.RingTheory.Norm.DVRResidue`, using the same quotient, residue map and
uniformizer-length identity. The final endpoints extend
`Colib.RingTheory.Charpoly.DVRResidue` to arbitrary residue fields.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing
open scoped TensorProduct

namespace Algebra

private theorem charpoly_lmul_eq_of_algebra_eq
    {k A : Type*} [Field k] [CommRing A] (a₁ a₂ : Algebra k A)
    (h₁ : letI := a₁; Module.Finite k A)
    (h₂ : letI := a₂; Module.Finite k A) (h : a₁ = a₂) (b : A) :
    (letI := a₁; letI := h₁; (lmul k A b).charpoly) =
      (letI := a₂; letI := h₂; (lmul k A b).charpoly) := by
  subst a₂
  rfl

/-- Scalar multiplication on a finite local algebra has the characteristic
polynomial on its actual residue field to the full self-length. -/
theorem charpoly_lmul_eq_residue_charpoly_pow_length
    {k B : Type*} [Field k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [IsLocalRing B] (b : B) :
    (lmul k B b).charpoly =
      (lmul k (ResidueField B) (residue B b)).charpoly ^ (Module.length B B).toNat := by
  let : IsLocalHom (algebraMap k B) :=
    ⟨fun x hx => isUnit_iff_ne_zero.mpr (fun h => hx.ne_zero (by rw [h, map_zero]))⟩
  have hB : IsFiniteLength B B := isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  have h := FiniteLengthEndomorphism.multiplication_charpoly_eq_pow_length k B B hB b
  dsimp only at h
  rw [FiniteLengthEndomorphism.charpoly_eq_map_charpoly] at h
  have hK : IsFiniteLength k (ResidueField B) :=
    Module.length_ne_top_iff.mp Module.length_ne_top
  have hres := FiniteLengthEndomorphism.charpoly_residue k (ResidueField B) hK
    (lmul (ResidueField k) (ResidueField B) (residue B b))
  rw [FiniteLengthEndomorphism.charpoly_eq_map_charpoly] at hres
  have hrestrict :
      (lmul (ResidueField k) (ResidueField B) (residue B b)).restrictScalars k =
        lmul k (ResidueField B) (residue B b) := by ext x; rfl
  rw [hrestrict] at hres
  rw [← hres, ← Polynomial.map_pow] at h
  exact Polynomial.map_injective (residue k) (residue k).injective h

variable (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R]
  [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- The literal closed fibre carries the coefficient reduction of the original
integral multiplication characteristic polynomial. -/
theorem charpoly_closedFiber (b : S) :
    let _ : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    let _ : IsScalarTower R (ResidueField R)
        (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : Module.Finite (ResidueField R)
        (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    (lmul (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b)).charpoly =
        (lmul R S b).charpoly.map (residue R) := by
  let : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R (ResidueField R)
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite (ResidueField R)
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let ε : (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≃ₐ[ResidueField R]
      (ResidueField R) ⊗[R] S :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)
  have h := charpoly_lmul_algEquiv (k := ResidueField R) ε
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b)
  have hε : ε (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) =
      (1 : ResidueField R) ⊗ₜ[R] b := rfl
  rw [hε, ← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange] at h
  exact h.symm

variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Reduction of the integral multiplication characteristic polynomial keeps the
full self-length of the actual closed fibre, with no residue characteristic restriction. -/
theorem residue_charpoly_lmul_eq_pow_length (b : S) :
    (lmul R S b).charpoly.map (residue R) =
      (lmul (ResidueField R) (ResidueField S) (residue S b)).charpoly ^
        (Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
          (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat := by
  let I := (maximalIdeal R).map (algebraMap R S)
  let B := S ⧸ I
  let : Algebra (ResidueField R) B :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R (ResidueField R) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hI : I ≠ ⊤ := ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing B := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R B) := by
    change IsLocalHom ((Ideal.Quotient.mk I).comp (algebraMap R S))
    infer_instance
  let : IsLocalHom (IsScalarTower.toAlgHom R S B) :=
    ⟨fun b hb => IsUnit.of_map (Ideal.Quotient.mk I) b hb⟩
  let : Module.Finite (ResidueField R) B := Module.Finite.of_restrictScalars_finite R _ _
  let φ : ResidueField S →ₐ[ResidueField R] ResidueField B :=
    ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R S B)
  have hφ (s : S) : φ (residue S s) = residue B (Ideal.Quotient.mk I s) :=
    ResidueField.mapAlgHom'_residue (IsScalarTower.toAlgHom R S B) s
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨b, rfl⟩ := residue_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨residue S s, hφ s⟩
  let ε : ResidueField S ≃ₐ[ResidueField R] ResidueField B :=
    AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have hc : (lmul (ResidueField R) (ResidueField B)
      (residue B (Ideal.Quotient.mk I b))).charpoly =
        (lmul (ResidueField R) (ResidueField S) (residue S b)).charpoly := by
    rw [← hφ]
    exact charpoly_lmul_algEquiv ε (residue S b)
  calc
    _ = (lmul (ResidueField R) B (Ideal.Quotient.mk I b)).charpoly :=
      (charpoly_closedFiber R S b).symm
    _ = (lmul (ResidueField R) (ResidueField B)
        (residue B (Ideal.Quotient.mk I b))).charpoly ^ (Module.length B B).toNat := by
      have halgebra : (ResidueField.algebra (R₀ := ResidueField R) B) =
          ResidueField.instAlgebra (R := R) (S := B) := by
        apply Algebra.algebra_ext
        intro x
        obtain ⟨r, rfl⟩ := residue_surjective x
        rfl
      have h := charpoly_lmul_eq_residue_charpoly_pow_length
        (k := ResidueField R) (B := B) (Ideal.Quotient.mk I b)
      have hchar := charpoly_lmul_eq_of_algebra_eq
        (ResidueField.algebra (R₀ := ResidueField R) B)
        (ResidueField.instAlgebra (R := R) (S := B))
        (by infer_instance) (by infer_instance) halgebra (residue B (Ideal.Quotient.mk I b))
      exact h.trans (congrArg (fun q : (ResidueField R)[X] =>
        q ^ (Module.length B B).toNat) hchar)
    _ = _ := congrArg (fun q => q ^ (Module.length B B).toNat) hc

end Algebra

namespace Algebra

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]

/-- The original multiplication characteristic polynomial reduces to the residue
characteristic polynomial with its actual ramification exponent, over any residue field. -/
theorem residue_charpoly_lmul_eq_pow_arbitrary
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (lmul R S b).charpoly.map (residue R) =
      (lmul (ResidueField R) (ResidueField S) (residue S b)).charpoly ^ e := by
  rw [residue_charpoly_lmul_eq_pow_length,
    IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he,
    ENat.toNat_natCast]

/-- Arbitrary-field reduction with both ramification and the full relative
residue-generator degree, retaining the literal minimal polynomial. -/
theorem residue_charpoly_lmul_eq_minpoly_pow_arbitrary
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^
        (e * Module.finrank
          (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) := by
  rw [residue_charpoly_lmul_eq_pow_arbitrary R S hπ hϖ u e he b,
    charpoly_lmul_eq_minpoly_pow_arbitrary, ← pow_mul, Nat.mul_comm]

/-- For the actual residue power-basis generator, the reduction exponent is
exactly the actual ramification exponent, also over finite residue fields. -/
theorem residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis_arbitrary
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b) :
    (lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^ e := by
  rw [residue_charpoly_lmul_eq_pow_arbitrary R S hπ hϖ u e he b, ← hB]
  congr 1
  rw [← LinearMap.charpoly_toMatrix _ B.basis]
  exact charpoly_leftMulMatrix B

end Algebra

end
