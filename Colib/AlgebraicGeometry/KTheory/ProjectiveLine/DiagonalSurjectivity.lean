/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalCoefficientKMaps
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalLastComparison
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.ProjectiveLineFormula
public import Colib.Util.References

/-! # Surjectivity from the actual diagonal

The quotient gives the original input, while the middle and first terms factor through
the untwisted and negatively twisted summands, respectively. The underlying Waldhausen
additivity equation expresses every class as a product of classes of the two summands.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [CompactSpace X]

local notation "P" => projectiveSpaceOver 1 X
local notation "W" Y => perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

/-- Surjectivity from a diagonal identity for the classes represented by bounded-below objects. -/
theorem projectiveLineKMap_surjective_of_diagonalIdentity (n : ℕ)
    (h : ∀ z : (BoundedBelowPerfect.waldhausen P).K n, ∃ a b : (W X).K n,
      KMap (BoundedBelowPerfect.inclusion_exact P) n z =
        KMap (projectiveLineFirstSummand_exact X) n a *
          (KMap (projectiveLineSecondSummand_exact X) n b)⁻¹) :
    Function.Surjective (projectiveLineKMap X n) := by
  let : IsProper (P ↘ X) := isProper_projectiveSpaceOver 1 X
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (P ↘ X)
  intro z
  obtain ⟨y, rfl⟩ := (BoundedBelowPerfect.inclusion_KMap_bijective P n).surjective z
  obtain ⟨a, b, h⟩ := h y
  exact ⟨(a, b⁻¹), by rw [projectiveLineKMap_apply, map_inv, h]⟩

local notation "π" => (P ↘ X)
local notation "Q" => CategoryTheory.Limits.pullback π π
local notation "p₁" => CategoryTheory.Limits.pullback.fst π π
local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local notation "d" => (IsExact.comp (FlasquePerfect.total_exact Q)
  (FlasquePerfect.perfectPushforward_exact p₁))
local notation "U" => FlasquePerfect.total_exact P
local notation "g₁" => FlasquePerfect.projectiveLineG₁_exact X
local notation "f" =>
  (IsExact.comp (BoundedBelowPerfect.projectiveLineDiagonalBoundedFirst_exact X) d)

/-- Use the actual diagonal additivity relation with the first-term projection formula. -/
theorem projectiveLineKMap_surjective_of_firstComparison (n : ℕ)
    (hfirst : ∀ z : (BoundedBelowPerfect.waldhausen P).K n,
      KMap f n z =
        KMap (projectiveLineSecondSummand_exact X) n (KMap g₁ n (KMap U n z))) :
    Function.Surjective (projectiveLineKMap X n) := by
  apply projectiveLineKMap_surjective_of_diagonalIdentity X n
  intro z
  let a := KMap (FlasquePerfect.projectiveLineG₀_exact X) n (KMap U n z)
  let b := KMap g₁ n (KMap U n z)
  refine ⟨a, b, ?_⟩
  have h := FlasquePerfect.projectiveLineDiagonalProjected_KMap_additivity X n z
  rw [FlasquePerfect.projectiveLineDiagonalMiddle_KMap_apply,
    FlasquePerfect.projectiveLineDiagonalLast_KMap, hfirst] at h
  change KMap (projectiveLineFirstSummand_exact X) n a =
    KMap (projectiveLineSecondSummand_exact X) n b *
      KMap (BoundedBelowPerfect.inclusion_exact P) n z at h
  exact eq_mul_inv_of_mul_eq ((Additivity.K_mul_comm (W P) n _ _).trans h.symm)

/-- The canonical two-summand map for the projective line is surjective. -/
theorem projectiveLineKMap_surjective (n : ℕ) : Function.Surjective (projectiveLineKMap X n) :=
  projectiveLineKMap_surjective_of_firstComparison X n
    (FlasquePerfect.projectiveLineDiagonalFirst_KMap_apply X n)

/-- The projective-line formula for every connective K-group of native perfect complexes. -/
@[colib_tag "COL-1261",
  colib_ref "ThomasonTrobaugh1990" "Theorem 4.1 and formula (4.1.3), p. 329"
    "specialization" "Rank-two trivial bundle and connective groups, with the negative-twist basis"]
def projectiveLineKEquiv (n : ℕ) : (W X).K n × (W X).K n ≃* (W P).K n :=
  projectiveLineKEquiv_of_surjective X n (projectiveLineKMap_surjective X n)

/-- The inverse consists of the two signed geometric direct-image coefficients. -/
@[colib_tag "COL-1261"]
theorem projectiveLineKEquiv_symm_apply (n : ℕ) (x : (W P).K n) :
    (projectiveLineKEquiv X n).symm x = projectiveLineCorrectedCoordinates X n x :=
  projectiveLineKEquiv_of_surjective_symm_apply X n (projectiveLineKMap_surjective X n) x

end AlgebraicGeometry.Scheme
