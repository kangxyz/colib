/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.EulerSign
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientIdentities

/-! # Assembly of the projective-line formula

With the ordered basis `(𝒪, 𝒪(-1))`, the coefficient maps are
`(Rπ_*, Rπ_*(- ⊗ 𝒪(-1)))`. The second coordinate is inverted on K-groups,
because `Rπ_* 𝒪(-2) ≅ 𝒪[-1]`. The diagonal supplies surjectivity of the
two-summand map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [CompactSpace X]

local notation "P" => projectiveSpaceOver 1 X
local notation "W" Y => perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

local notation "L" => (twistOver 1 X (-1))

local instance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-- The actual second coefficient of the twisted summand is the input with a minus sign. -/
theorem projectiveLineGeometricKMap_secondSummand_snd (n : ℕ) (b : (W X).K n) :
    (projectiveLineGeometricKMap X n (KMap (projectiveLineSecondSummand_exact X) n b)).2 =
      b⁻¹ := by
  obtain ⟨y, rfl⟩ := (BoundedBelowPerfect.inclusion_KMap_bijective X n).surjective b
  let A := BoundedBelowPerfect.flatPullback_exact (P ↘ X)
  let T := BoundedBelowPerfect.tensorVectorBundleRight_exact L
  let U := FlasquePerfect.total_exact P
  rw [projectiveLineKMap_summand_on_boundedBelow X (A.comp T)
    (projectiveLineSecondSummand_exact X) (projectiveLineSecondSummandInclusionIso X) n y,
    projectiveLineGeometricKMap_of_flasque]
  change KMap (FlasquePerfect.projectiveLineG₁_exact X) n (KMap ((A.comp T).comp U) n y) = _
  rw [← KMap_comp_KMap (A.comp T) U n, ← KMap_comp_KMap A T n]
  exact FlasquePerfect.projectiveLineG₁_negative_KMap_apply X n y

/-- The geometric coordinates, corrected by the sign on the second summand. -/
def projectiveLineCorrectedCoordinates (n : ℕ) (x : (W P).K n) :
    (W X).K n × (W X).K n :=
  let y := projectiveLineGeometricKMap X n x
  (y.1, y.2⁻¹)

/-- The signed coefficient matrix gives the left-inverse identity for the actual map. -/
theorem projectiveLineCorrectedCoordinates_leftInverse (n : ℕ) :
    Function.LeftInverse (projectiveLineCorrectedCoordinates X n) (projectiveLineKMap X n) := by
  rintro ⟨a, b⟩
  apply _root_.Prod.ext <;>
    simp [projectiveLineCorrectedCoordinates, projectiveLineKMap_apply, map_mul,
      projectiveLineGeometricKMap_firstSummand, projectiveLineGeometricKMap_secondSummand_fst,
      projectiveLineGeometricKMap_secondSummand_snd]

/-- Surjectivity from the diagonal makes the two-summand map an equivalence. -/
def projectiveLineKEquiv_of_surjective (n : ℕ)
    (h : Function.Surjective (projectiveLineKMap X n)) :
    (W X).K n × (W X).K n ≃* (W P).K n :=
  MulEquiv.ofBijective (projectiveLineKMap X n)
    ⟨(projectiveLineCorrectedCoordinates_leftInverse X n).injective, h⟩

/-- The inverse of the equivalence is the signed geometric coefficient map. -/
theorem projectiveLineKEquiv_of_surjective_symm_apply (n : ℕ)
    (h : Function.Surjective (projectiveLineKMap X n)) (x : (W P).K n) :
    (projectiveLineKEquiv_of_surjective X n h).symm x =
      projectiveLineCorrectedCoordinates X n x := by
  obtain ⟨y, rfl⟩ := h x
  exact ((projectiveLineKEquiv_of_surjective X n h).symm_apply_apply y).trans
    (projectiveLineCorrectedCoordinates_leftInverse X n y).symm

end AlgebraicGeometry.Scheme
