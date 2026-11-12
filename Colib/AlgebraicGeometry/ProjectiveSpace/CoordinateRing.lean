/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Polynomial coordinates on the native projective chart

The chart ring is the actual degree-zero homogeneous localization of the polynomial ring.
The comparison sends constants to degree-zero fractions and variables to the original ratios.
For a finite index type its bijectivity is transported from the pinned Stacks chart comparison
by renaming the homogeneous variables, without changing the projective-space model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial HomogeneousLocalization CategoryTheory

universe u v w

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (k : Type u) [CommRing k] (ι : Type v) (i : ι)

/-- The actual degree-zero localization on the `i`-th projective chart. -/
abbrev coordinateRing := Away (homogeneousSubmodule ι k) (X i)

/-- A coefficient as a degree-zero fraction with denominator one. -/
def coordinateRingCoefficient (a : k) : coordinateRing k ι i :=
  Away.mk _ (isHomogeneous_X k i) 0 (C a) (by simp)

/-- The original homogeneous coordinate ratio `X j / X i`. -/
def coordinateRatio (j : ι) : coordinateRing k ι i :=
  Away.mk _ (isHomogeneous_X k i) 1 (X j) (by simpa using isHomogeneous_X k j)

/-- The canonical coefficient homomorphism into a projective chart. -/
def coordinateCoefficientHom : k →+* coordinateRing k ι i :=
  (algebraMap (homogeneousSubmodule ι k 0) (coordinateRing k ι i)).comp
    (algebraMap k (homogeneousSubmodule ι k 0))

@[simp]
theorem coordinateCoefficientHom_apply (a : k) :
    coordinateCoefficientHom k ι i a = coordinateRingCoefficient k ι i a := by
  apply HomogeneousLocalization.val_injective
  simp only [coordinateCoefficientHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_eq,
    coordinateRingCoefficient]
  change Localization.mk ((algebraMap k (homogeneousSubmodule ι k 0) a :
    homogeneousSubmodule ι k 0) : MvPolynomial ι k) 1 = _
  rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  rfl

/-- Evaluate affine variables at the original homogeneous coordinate ratios. -/
def polynomialToCoordinateRing : MvPolynomial {j : ι // j ≠ i} k →+* coordinateRing k ι i :=
  eval₂Hom (coordinateCoefficientHom k ι i) (fun j => coordinateRatio k ι i j.val)

@[simp]
theorem polynomialToCoordinateRing_C (a : k) :
    polynomialToCoordinateRing k ι i (C a) = coordinateRingCoefficient k ι i a := by
  simp [polynomialToCoordinateRing]

@[simp]
theorem polynomialToCoordinateRing_X (j : {j : ι // j ≠ i}) :
    polynomialToCoordinateRing k ι i (X j) = coordinateRatio k ι i j.val :=
  eval₂Hom_X' _ _ _

/-- Set the pivot homogeneous variable to one, retaining the names of all other variables. -/
def coordinateSetOne : MvPolynomial ι k →+* MvPolynomial {j : ι // j ≠ i} k :=
  letI := Classical.decEq ι
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp]
theorem coordinateSetOne_X_self : coordinateSetOne k ι i (X i) = 1 := by
  simp [coordinateSetOne]

/-- Dehomogenize a degree-zero fraction by setting the pivot coordinate to one. -/
def coordinateRingToPolynomial : coordinateRing k ι i →+* MvPolynomial {j : ι // j ≠ i} k :=
  (Localization.awayLift (coordinateSetOne k ι i) (X i)
    (by simp)).comp (algebraMap (coordinateRing k ι i) (Localization.Away (X i)))

@[simp]
theorem coordinateRingToPolynomial_mk (n : ℕ) (a : MvPolynomial ι k)
    (ha : a ∈ homogeneousSubmodule ι k (n • 1)) :
    coordinateRingToPolynomial k ι i (Away.mk _ (isHomogeneous_X k i) n a ha) =
      coordinateSetOne k ι i a := by
  change Localization.awayLift (coordinateSetOne k ι i) (X i) (by simp)
    (Localization.mk a ⟨X i ^ n, n, rfl⟩) = _
  rw [Localization.awayLift_mk _ _ _ 1 (by simp) n]
  simp

@[simp]
theorem coordinateRingToPolynomial_coefficient (a : k) :
    coordinateRingToPolynomial k ι i (coordinateRingCoefficient k ι i a) = C a := by
  simp [coordinateRingCoefficient, coordinateSetOne]

@[simp]
theorem coordinateRingToPolynomial_ratio (j : {j : ι // j ≠ i}) :
    coordinateRingToPolynomial k ι i (coordinateRatio k ι i j.val) = X j := by
  simp [coordinateRatio, coordinateSetOne, j.property]

@[simp]
theorem coordinateRatio_self : coordinateRatio k ι i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [coordinateRatio, Away.val_mk, pow_one, HomogeneousLocalization.val_one]
  exact Localization.mk_self (S := Submonoid.powers (X i : MvPolynomial ι k))
    ⟨X i, 1, by simp⟩

/-- Dehomogenization is a left inverse to the original ratio evaluation. -/
theorem coordinateRingToPolynomial_comp_polynomialToCoordinateRing :
    (coordinateRingToPolynomial k ι i).comp (polynomialToCoordinateRing k ι i) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro a <;> simp

section Rename

variable {ι} {κ : Type w} (f : ι → κ)

/-- Rename homogeneous variables as a graded ring homomorphism. -/
def coordinateRenameGraded : homogeneousSubmodule ι k →+*ᵍ homogeneousSubmodule κ k where
  toRingHom := (rename f).toRingHom
  map_mem h := MvPolynomial.IsHomogeneous.rename_isHomogeneous h

/-- Renaming homogeneous variables induces the corresponding map of native chart rings. -/
def coordinateRingRename : coordinateRing k ι i →+* coordinateRing k κ (f i) :=
  HomogeneousLocalization.map (coordinateRenameGraded k f) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp [coordinateRenameGraded]⟩)

@[simp]
theorem coordinateRingRename_mk (n : ℕ) (a : MvPolynomial ι k)
    (ha : a ∈ homogeneousSubmodule ι k (n • 1)) :
    coordinateRingRename k i f (Away.mk _ (isHomogeneous_X k i) n a ha) =
      Away.mk _ (isHomogeneous_X k (f i)) n (rename f a)
        (MvPolynomial.IsHomogeneous.rename_isHomogeneous ha) := by
  simp only [coordinateRingRename, Away.mk, HomogeneousLocalization.map_mk,
    coordinateRenameGraded]
  congr 1
  simp

/-- An equivalence of homogeneous indices is surjective on the actual chart rings. -/
theorem coordinateRingRename_surjective (e : ι ≃ κ) :
    Function.Surjective (coordinateRingRename k i e) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (isHomogeneous_X k (e i)) z
  refine ⟨Away.mk _ (isHomogeneous_X k i) n (rename e.symm a)
    (MvPolynomial.IsHomogeneous.rename_isHomogeneous ha), ?_⟩
  simp only [coordinateRingRename_mk]
  congr 1
  simp

end Rename

/-- Transport the pinned Stacks chart theorem along an equivalence of homogeneous indices. -/
theorem polynomialToCoordinateRing_surjective_of_equiv (n : ℕ)
    (e : Fin (n + 1) ≃ ι) (j : Fin (n + 1)) :
    Function.Surjective (polynomialToCoordinateRing k ι (e j)) := by
  classical
  let e' : {a : Fin (n + 1) // a ≠ j} ≃ {a : ι // a ≠ e j} :=
    e.subtypeEquiv (fun a => by simp)
  have hcomp : (coordinateRingRename k j e).comp
      (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv k n j).toRingHom =
      (polynomialToCoordinateRing k ι (e j)).comp (rename e').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv_apply,
        Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_C,
        Stacks.AlgebraicGeometry.ProjPolyChart.coeffToAway_eq_mk,
        coordinateRingRename_mk, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        rename_C, polynomialToCoordinateRing_C, coordinateRingCoefficient]
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv_apply,
        Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_X,
        Stacks.AlgebraicGeometry.ProjPolyChart.chartCoord,
        coordinateRingRename_mk, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        rename_X, polynomialToCoordinateRing_X, coordinateRatio]
      rfl
  have hs := (coordinateRingRename_surjective k j e).comp
    (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv k n j).surjective
  rw [show (coordinateRingRename k j e) ∘
      (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv k n j) =
      (polynomialToCoordinateRing k ι (e j)) ∘ rename e' from
      congrArg DFunLike.coe hcomp] at hs
  exact hs.of_comp

/-- Bijectivity for finite homogeneous indices is the pinned Stacks chart theorem after
renaming both homogeneous variables and their affine ratios. -/
theorem polynomialToCoordinateRing_surjective [Finite ι] :
    Function.Surjective (polynomialToCoordinateRing k ι i) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))
  let e : Fin (n + 1) ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  have h := polynomialToCoordinateRing_surjective_of_equiv k ι n e (e.symm i)
  rw [e.apply_symm_apply] at h
  exact h

/-- The two actual coordinate homomorphisms are inverse. -/
theorem polynomialToCoordinateRing_comp_coordinateRingToPolynomial [Finite ι] :
    (polynomialToCoordinateRing k ι i).comp (coordinateRingToPolynomial k ι i) =
      RingHom.id _ := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := polynomialToCoordinateRing_surjective k ι i z
  have h := RingHom.congr_fun
    (coordinateRingToPolynomial_comp_polynomialToCoordinateRing k ι i) p
  simpa using congrArg (polynomialToCoordinateRing k ι i) h

/-- The native chart ring is the polynomial ring in the unchanged non-pivot coordinates. -/
def coordinateRingEquivPolynomial [Finite ι] :
    coordinateRing k ι i ≃+* MvPolynomial {j : ι // j ≠ i} k where
  __ := coordinateRingToPolynomial k ι i
  invFun := polynomialToCoordinateRing k ι i
  left_inv := RingHom.congr_fun
    (polynomialToCoordinateRing_comp_coordinateRingToPolynomial k ι i)
  right_inv := RingHom.congr_fun
    (coordinateRingToPolynomial_comp_polynomialToCoordinateRing k ι i)

/-- The original coordinate chart as the native `Proj.awayι` open immersion. -/
def coordinateChart : Spec (.of (coordinateRing k ι i)) ⟶
    Proj (homogeneousSubmodule ι k) :=
  Proj.awayι _ (X i) (isHomogeneous_X k i) Nat.one_pos

instance : IsOpenImmersion (coordinateChart k ι i) := by
  unfold coordinateChart
  infer_instance

end AlgebraicGeometry.ProjectiveSpace
