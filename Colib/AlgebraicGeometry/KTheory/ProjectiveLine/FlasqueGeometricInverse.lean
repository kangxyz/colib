/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalSurjectivity
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectShiftSign

/-! # The projective-line inverse with the actual cochain shift -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "W" Y =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

/-- The second coefficient is the actual twist, Godement total, direct image and shift. -/
def projectiveLineShiftedCoefficient :=
  FlasquePerfect.projectiveLineG₁ X ⋙ perfectShift X.toRingedSpace 1

/-- The literal composite of the four functors is Waldhausen exact. -/
theorem projectiveLineShiftedCoefficient_exact :
    IsExact (FlasquePerfect.waldhausen P).cof (FlasquePerfect.waldhausen P).weq
      (W X).cof (W X).weq (projectiveLineShiftedCoefficient X) :=
  (FlasquePerfect.projectiveLineG₁_exact X).comp (perfectShift_exact X.toRingedSpace 1)

/-- The two literal coefficients on flasque representatives, including the cochain shift. -/
def projectiveLineShiftedCoefficientPair (n : ℕ) :
    (FlasquePerfect.waldhausen P).K n →* (W X).K n × (W X).K n :=
  (KMap (FlasquePerfect.projectiveLineG₀_exact X) n).prod
    (KMap (projectiveLineShiftedCoefficient_exact X) n)

section
variable [CompactSpace X]

/-- Transport of the two actual coefficient maps recovers the signed geometric coordinates. -/
theorem projectiveLineShiftedCoefficientPair_apply (n : ℕ)
    (a : (FlasquePerfect.waldhausen P).K n) :
    projectiveLineShiftedCoefficientPair X n a =
      projectiveLineCorrectedCoordinates X n (projectiveLineFlasqueKEquiv X n a) := by
  rw [projectiveLineCorrectedCoordinates, projectiveLineGeometricKMap_of_flasque]
  apply _root_.Prod.ext
  · rfl
  · change KMap ((FlasquePerfect.projectiveLineG₁_exact X).comp
      (perfectShift_exact X.toRingedSpace 1)) n a =
        (KMap (FlasquePerfect.projectiveLineG₁_exact X) n a)⁻¹
    rw [← KMap_comp_KMap]
    exact perfectShift_KMap_one_apply X.toRingedSpace n _

/-- The actual shifted coefficient maps, transported by the flasque inclusion. -/
def projectiveLineShiftedGeometricKMap (n : ℕ) :
    (W P).K n →* (W X).K n × (W X).K n :=
  (projectiveLineShiftedCoefficientPair X n).comp
    (projectiveLineFlasqueKEquiv X n).symm.toMonoidHom

/-- The actual shifted functor yields the existing signed geometric inverse. -/
theorem projectiveLineShiftedGeometricKMap_apply (n : ℕ) (a : (W P).K n) :
    projectiveLineShiftedGeometricKMap X n a = projectiveLineCorrectedCoordinates X n a := by
  change projectiveLineShiftedCoefficientPair X n ((projectiveLineFlasqueKEquiv X n).symm a) = _
  rw [projectiveLineShiftedCoefficientPair_apply, MulEquiv.apply_symm_apply]

/-- Composing the actual shifted coefficients with the native two-summand map gives the identity. -/
theorem projectiveLineShiftedGeometricKMap_comp (n : ℕ) :
    (projectiveLineShiftedGeometricKMap X n).comp (projectiveLineKMap X n) =
      MonoidHom.id ((W X).K n × (W X).K n) := by
  ext a : 1
  exact (projectiveLineShiftedGeometricKMap_apply X n _).trans
    (projectiveLineCorrectedCoordinates_leftInverse X n a)

/-- The other composite follows by surjectivity of the very same native two-summand map. -/
theorem projectiveLineKMap_comp_shiftedGeometricKMap (n : ℕ) :
    (projectiveLineKMap X n).comp (projectiveLineShiftedGeometricKMap X n) =
      MonoidHom.id ((W P).K n) := by
  ext a : 1
  obtain ⟨b, rfl⟩ := projectiveLineKMap_surjective X n a
  change projectiveLineKMap X n
    ((projectiveLineShiftedGeometricKMap X n).comp (projectiveLineKMap X n) b) = _
  rw [projectiveLineShiftedGeometricKMap_comp]
  rfl

end

local notation "B" Y => BoundedBelowPerfect.waldhausen Y
local notation "F" Y => FlasquePerfect.waldhausen Y
local notation "π" => (P ↘ X)
local notation "L" => twistOver 1 X (-1)
local notation "i" => FlasquePerfect.inclusion_exact X
local notation "a₀" => BoundedBelowPerfect.flatPullback_exact π
local notation "u₀" => FlasquePerfect.total_exact P

local instance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
    (R := (P).ringCatSheaf) L :=
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local notation "t₁" => BoundedBelowPerfect.tensorVectorBundleRight_exact L

local instance : HasBinaryCoproducts (BoundedBelowPerfect.Obj P) :=
  Additivity.hasBinaryCoproducts (B P)

/-- The original forward functor forms the two summands before the Godement total. -/
def projectiveLineFlasqueTwoSummands :=
  CategoryTheory.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ FlasquePerfect.inclusion X ⋙
      BoundedBelowPerfect.flatPullback π)
    (CategoryTheory.Prod.snd _ _ ⋙ FlasquePerfect.inclusion X ⋙
      (BoundedBelowPerfect.flatPullback π ⋙ BoundedBelowPerfect.tensorVectorBundleRight L)) ⋙
    FlasquePerfect.total P

/-- The literal forward functor is exact in the flasque perfect categories. -/
theorem projectiveLineFlasqueTwoSummands_exact :
    IsExact (Product.productStructure (F X) (F X)).cof
      (Product.productStructure (F X) (F X)).weq (F P).cof (F P).weq
      (projectiveLineFlasqueTwoSummands X) :=
  (Additivity.sumFunctor_isExact _ _
    ((Product.fst_exact _ _).comp ((i).comp a₀))
    ((Product.snd_exact _ _).comp ((i).comp ((a₀).comp t₁)))).comp u₀

/-- The chosen-zero group map of the actual flasque two-summand functor. -/
def projectiveLineFlasqueKMap (n : ℕ) :
    (F X).K n × (F X).K n →* (F P).K n :=
  (KMap (projectiveLineFlasqueTwoSummands_exact X) n).comp
    (Product.KEquiv (F X) (F X) n).symm.toMonoidHom

variable [CompactSpace X]

/-- The actual forward map commutes with the literal flasque inclusions. -/
theorem projectiveLineFlasqueKMap_inclusion (n : ℕ) (a b : (F X).K n) :
    projectiveLineFlasqueKEquiv X n (projectiveLineFlasqueKMap X n (a, b)) =
      projectiveLineKMap X n
        (KMap (FlasquePerfect.perfectInclusion_exact X) n a,
          KMap (FlasquePerfect.perfectInclusion_exact X) n b) := by
  let z := (Product.KEquiv (F X) (F X) n).symm (a, b)
  let ea := (Product.fst_exact (F X) (F X)).comp ((i).comp a₀)
  let eb := (Product.snd_exact (F X) (F X)).comp ((i).comp ((a₀).comp t₁))
  have hz : (KMap (Product.fst_exact (F X) (F X)) n z,
      KMap (Product.snd_exact (F X) (F X)) n z) = (a, b) :=
    (Product.KEquiv (F X) (F X) n).apply_symm_apply _
  change projectiveLineFlasqueKEquiv X n
    (KMap ((Additivity.sumFunctor_isExact _ _ ea eb).comp u₀) n z) = _
  rw [← KMap_comp_KMap (Additivity.sumFunctor_isExact _ _ ea eb) u₀ n,
    MonoidHom.comp_apply, Additivity.KMap_sum_apply _ _ ea eb n z,
    map_mul, map_mul, projectiveLineKMap_apply]
  have ha := congrArg _root_.Prod.fst hz
  have hb := congrArg _root_.Prod.snd hz
  change KMap (Product.fst_exact (F X) (F X)) n z = a at ha
  change KMap (Product.snd_exact (F X) (F X)) n z = b at hb
  congr 1
  · change projectiveLineFlasqueKEquiv X n (KMap u₀ n (KMap
      ((Product.fst_exact (F X) (F X)).comp ((i).comp a₀)) n z)) = _
    rw [← KMap_comp_KMap (Product.fst_exact (F X) (F X)) ((i).comp a₀),
      MonoidHom.comp_apply, ha, ← KMap_comp_KMap i a₀, MonoidHom.comp_apply]
    rw [← MonoidHom.comp_apply (KMap u₀ n) (KMap a₀ n), KMap_comp_KMap a₀ u₀]
    simpa only [MonoidHom.comp_apply, FlasquePerfect.perfectInclusion_KMap_eq] using
      (projectiveLineKMap_summand_on_boundedBelow X a₀ (projectiveLineFirstSummand_exact X)
        (BoundedBelowPerfect.flatPullbackInclusionIso π) n (KMap i n a)).symm
  · change projectiveLineFlasqueKEquiv X n (KMap u₀ n (KMap
      ((Product.snd_exact (F X) (F X)).comp ((i).comp ((a₀).comp t₁))) n z)) = _
    rw [← KMap_comp_KMap (Product.snd_exact (F X) (F X)) ((i).comp ((a₀).comp t₁)),
      MonoidHom.comp_apply, hb, ← KMap_comp_KMap i ((a₀).comp t₁), MonoidHom.comp_apply]
    rw [← MonoidHom.comp_apply (KMap u₀ n) (KMap ((a₀).comp t₁) n),
      KMap_comp_KMap ((a₀).comp t₁) u₀]
    simpa only [MonoidHom.comp_apply, FlasquePerfect.perfectInclusion_KMap_eq] using
      (projectiveLineKMap_summand_on_boundedBelow X ((a₀).comp t₁)
        (projectiveLineSecondSummand_exact X) (projectiveLineSecondSummandInclusionIso X)
        n (KMap i n b)).symm

end AlgebraicGeometry.Scheme
