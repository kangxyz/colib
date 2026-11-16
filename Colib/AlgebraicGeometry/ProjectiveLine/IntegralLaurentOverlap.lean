/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Laurent coordinates on the integral projective-line overlap

The overlap in the graded polynomial Proj is the homogeneous localization at
the product of the two variables. The two affine chart ratios restrict there
as reciprocal elements.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization
open SetLike
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace AlgebraicGeometry.Scheme.ProjectiveLine

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

local notation "𝒜" => polyGrading R 1
local notation "x₀" => (MvPolynomial.X 0 : MvPolynomial (Fin 2) R)
local notation "x₁" => (MvPolynomial.X 1 : MvPolynomial (Fin 2) R)

/-- The first affine chart ratio, transported by the actual homogeneous localization map. -/
def forwardOverlapCoordinate : Away 𝒜 (x₀ * x₁) :=
  awayMap 𝒜 (X_mem_one R 1 1) rfl (chartCoord R 1 0 ⟨1, by decide⟩)

/-- The inverse affine chart ratio, transported by the other actual localization map. -/
def inverseOverlapCoordinate : Away 𝒜 (x₀ * x₁) :=
  awayMap 𝒜 (X_mem_one R 1 0) (mul_comm x₀ x₁)
    (chartCoord R 1 1 ⟨0, by decide⟩)

/-- The positive and inverted chart coordinates become mutually inverse on the overlap. -/
theorem overlapCoordinates_mul :
    forwardOverlapCoordinate R * inverseOverlapCoordinate R = 1 := by
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp only [val_mul, val_one, forwardOverlapCoordinate, inverseOverlapCoordinate, chartCoord,
    awayMap_mk, pow_one, Away.val_mk]
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  simp only [Submonoid.coe_mul, mul_one]
  ring

/-- The polynomial coordinate in the positive chart is exactly the ratio `T₁/T₀`. -/
def positiveCoordinateEquiv : Polynomial R ≃+* Away 𝒜 x₀ :=
  (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.toRingEquiv.trans
    ((MvPolynomial.renameEquiv R (finSuccAboveEquiv (0 : Fin 2))).toRingEquiv.trans
      (chartEquiv R 1 0))

theorem positiveCoordinateEquiv_X :
    positiveCoordinateEquiv R Polynomial.X =
      Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1) := by
  simp only [positiveCoordinateEquiv, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.eval₂_X,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, chartEquiv_apply, chartHom_X]
  have h : finSuccAboveEquiv (0 : Fin 2) (default : Fin 1) = ⟨1, by decide⟩ :=
    Subtype.ext (by decide)
  rw [h]
  unfold chartCoord Away.isLocalizationElem
  simp only [pow_one]

/-- The native Proj overlap ring is the localization of the positive chart at its coordinate. -/
def integralLaurentEquiv : LaurentPolynomial R ≃+* Away 𝒜 (x₀ * x₁) := by
  let := (awayMap 𝒜 (X_mem_one R 1 1) (rfl : x₀ * x₁ = x₀ * x₁)).toAlgebra
  let : IsLocalization.Away
      (Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1))
      (Away 𝒜 (x₀ * x₁)) := Away.isLocalization_mul
        (X_mem_one R 1 0) (X_mem_one R 1 1) rfl (by decide)
  refine IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers (Polynomial.X : Polynomial R))
      (T := Submonoid.powers (Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1)))
      (LaurentPolynomial R) (Away 𝒜 (x₀ * x₁))
    (positiveCoordinateEquiv R) ?_
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (positiveCoordinateEquiv_X R)

/-- The polynomial coordinate in the other chart is `T₀/T₁`. -/
def inverseCoordinateEquiv : Polynomial R ≃+* Away 𝒜 x₁ :=
  (MvPolynomial.uniqueAlgEquiv R (Fin 1)).symm.toRingEquiv.trans
    ((MvPolynomial.renameEquiv R (finSuccAboveEquiv (1 : Fin 2))).toRingEquiv.trans
      (chartEquiv R 1 1))

theorem inverseCoordinateEquiv_X :
    inverseCoordinateEquiv R Polynomial.X = chartCoord R 1 1 ⟨0, by decide⟩ := by
  simp only [inverseCoordinateEquiv, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.eval₂_X,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, chartEquiv_apply, chartHom_X]
  rfl


/-- The positive polynomial leg is the actual localization structure map. -/
theorem integralLaurentEquiv_toLaurent (a : Polynomial R) :
    integralLaurentEquiv R (Polynomial.toLaurent a) =
      awayMap 𝒜 (X_mem_one R 1 1) rfl (positiveCoordinateEquiv R a) := by
  let := (awayMap 𝒜 (X_mem_one R 1 1) (rfl : x₀ * x₁ = x₀ * x₁)).toAlgebra
  let : IsLocalization.Away
      (Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1))
      (Away 𝒜 (x₀ * x₁)) := Away.isLocalization_mul
        (X_mem_one R 1 0) (X_mem_one R 1 1) rfl (by decide)
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  unfold integralLaurentEquiv
  rw [IsLocalization.ringEquivOfRingEquiv_apply, IsLocalization.map_eq]
  rfl


/-- The overlap ring equivalence sends the forward Laurent generator to the first chart ratio. -/
theorem integralLaurentEquiv_T_one :
    integralLaurentEquiv R (LaurentPolynomial.T 1) = forwardOverlapCoordinate R := by
  rw [← Polynomial.toLaurent_X, integralLaurentEquiv_toLaurent, positiveCoordinateEquiv_X]
  congr 1
  unfold chartCoord Away.isLocalizationElem
  simp only [pow_one]

/-- The inverse Laurent generator is precisely the second chart ratio. -/
theorem integralLaurentEquiv_T_neg_one :
    integralLaurentEquiv R (LaurentPolynomial.T (-1)) = inverseOverlapCoordinate R := by
  have h : forwardOverlapCoordinate R * integralLaurentEquiv R
      (LaurentPolynomial.T (-1)) = 1 := by
    rw [← integralLaurentEquiv_T_one, ← map_mul, ← LaurentPolynomial.T_add]
    simp
  calc
    integralLaurentEquiv R (LaurentPolynomial.T (-1)) =
        (inverseOverlapCoordinate R * forwardOverlapCoordinate R) *
          integralLaurentEquiv R (LaurentPolynomial.T (-1)) := by
      rw [mul_comm (inverseOverlapCoordinate R) (forwardOverlapCoordinate R),
        overlapCoordinates_mul, one_mul]
    _ = inverseOverlapCoordinate R := by rw [mul_assoc, h, mul_one]


/-- The two localized coefficient inclusions remain literally the same. -/
theorem overlapCoefficient_eq (r : R) :
    awayMap 𝒜 (X_mem_one R 1 1) rfl (coeffToAway R 1 0 r) =
      awayMap 𝒜 (X_mem_one R 1 0) (mul_comm x₀ x₁) (coeffToAway R 1 1 r) := by
  change awayMap 𝒜 (X_mem_one R 1 1) rfl
      (fromZeroRingHom 𝒜 _ (algebraMap R (𝒜 0) r)) =
    awayMap 𝒜 (X_mem_one R 1 0) (mul_comm x₀ x₁)
      (fromZeroRingHom 𝒜 _ (algebraMap R (𝒜 0) r))
  rw [awayMap_fromZeroRingHom, awayMap_fromZeroRingHom]

/-- The positive ring square identifies the actual `Polynomial.toLaurent` leg. -/
theorem integralLaurentEquiv_positiveLeg :
    (integralLaurentEquiv R).toRingHom.comp Polynomial.toLaurent =
      (awayMap 𝒜 (X_mem_one R 1 1) rfl).comp (positiveCoordinateEquiv R).toRingHom :=
  RingHom.ext (integralLaurentEquiv_toLaurent R)

/-- The ring square with the inverse polynomial chart uses the actual Laurent inversion. -/
theorem integralLaurentEquiv_inverseLeg :
    (integralLaurentEquiv R).toRingHom.comp
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) =
      (awayMap 𝒜 (X_mem_one R 1 0) (mul_comm x₀ x₁)).comp
        (inverseCoordinateEquiv R).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change integralLaurentEquiv R (LaurentPolynomial.invert
        (Polynomial.toLaurent (Polynomial.C r))) = _
    rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C, ← Polynomial.toLaurent_C,
      integralLaurentEquiv_toLaurent]
    have h₀ : positiveCoordinateEquiv R (Polynomial.C r) = coeffToAway R 1 0 r := by
      simp [positiveCoordinateEquiv, chartEquiv_apply, chartHom]
    have h₁ : inverseCoordinateEquiv R (Polynomial.C r) = coeffToAway R 1 1 r := by
      simp [inverseCoordinateEquiv, chartEquiv_apply, chartHom]
    rw [h₀]
    change _ = awayMap 𝒜 (X_mem_one R 1 0) (mul_comm x₀ x₁)
      (inverseCoordinateEquiv R (Polynomial.C r))
    rw [h₁]
    exact overlapCoefficient_eq R r
  · change integralLaurentEquiv R (LaurentPolynomial.invert
        (Polynomial.toLaurent Polynomial.X)) = _
    rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T,
      integralLaurentEquiv_T_neg_one]
    change inverseOverlapCoordinate R =
      awayMap 𝒜 (X_mem_one R 1 0) (mul_comm x₀ x₁) (inverseCoordinateEquiv R Polynomial.X)
    rw [inverseCoordinateEquiv_X]
    rfl



end AlgebraicGeometry.Scheme.ProjectiveLine
