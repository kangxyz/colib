/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueGeometricInverse
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueActualCoefficients

/-! # The actual two composites on flasque projective-line K-groups -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "L" => twistOver 1 X (-1)
local notation "F" Y => FlasquePerfect.waldhausen Y
local notation "W" Y =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local instance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
    (R := (P).ringCatSheaf) L :=
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local notation "g₀" => FlasquePerfect.flasquePerfectPushforward_exact π

/-- The negative coefficient retains the actual shift within the flasque target. -/
def projectiveLineFlasqueShiftedCoefficient : FlasquePerfect.Obj P ⥤ FlasquePerfect.Obj X :=
  ((FlasquePerfect.inclusion P ⋙ BoundedBelowPerfect.tensorVectorBundleRight L) ⋙
    FlasquePerfect.total P) ⋙
      (FlasquePerfect.flasquePerfectPushforward π ⋙ FlasquePerfect.flasquePerfectShift X 1)

theorem projectiveLineFlasqueShiftedCoefficient_exact :
    IsExact (F P).cof (F P).weq (F X).cof (F X).weq
      (projectiveLineFlasqueShiftedCoefficient X) :=
  (((FlasquePerfect.inclusion_exact P).comp
    (BoundedBelowPerfect.tensorVectorBundleRight_exact L)).comp
    (FlasquePerfect.total_exact P)).comp
    ((g₀).comp (FlasquePerfect.flasquePerfectShift_exact X 1))

/-- The literal pair of chosen-zero K-maps of the two coefficient functors. -/
def projectiveLineFlasqueCoefficientPair (n : ℕ) :
    (F P).K n →* (F X).K n × (F X).K n :=
  (Product.KEquiv (F X) (F X) n).toMonoidHom.comp
    (KMap (Product.pair_exact (F P) (F X) (F X) g₀
      (projectiveLineFlasqueShiftedCoefficient_exact X)) n)

/-- The two projections recover the actual coefficient K-maps. -/
theorem projectiveLineFlasqueCoefficientPair_apply (n : ℕ) (a : (F P).K n) :
    projectiveLineFlasqueCoefficientPair X n a =
      (KMap g₀ n a, KMap (projectiveLineFlasqueShiftedCoefficient_exact X) n a) :=
  Product.KEquiv_pair_apply (F P) (F X) (F X) g₀
    (projectiveLineFlasqueShiftedCoefficient_exact X) n a

local notation "j" => FlasquePerfect.perfectInclusion_exact X


/-- Literal inclusion preserves both coefficient coordinates, including the shifted one. -/
theorem projectiveLineFlasqueCoefficientPair_inclusion (n : ℕ) (a : (F P).K n) :
    (KMap j n (projectiveLineFlasqueCoefficientPair X n a).1,
      KMap j n (projectiveLineFlasqueCoefficientPair X n a).2) =
        projectiveLineShiftedCoefficientPair X n a := by
  rw [projectiveLineFlasqueCoefficientPair_apply]
  apply _root_.Prod.ext
  · change KMap j n (KMap g₀ n a) = KMap (FlasquePerfect.projectiveLineG₀_exact X) n a
    rw [← MonoidHom.comp_apply (KMap j n) (KMap g₀ n), KMap_comp_KMap]
    rfl
  · change KMap j n (KMap (projectiveLineFlasqueShiftedCoefficient_exact X) n a) =
      KMap (projectiveLineShiftedCoefficient_exact X) n a
    rw [← MonoidHom.comp_apply (KMap j n)
      (KMap (projectiveLineFlasqueShiftedCoefficient_exact X) n), KMap_comp_KMap]
    rfl

variable [CompactSpace X]

/-- The two actual flasque functors give the left inverse in every connective degree. -/
theorem projectiveLineFlasqueCoefficientPair_comp (n : ℕ) :
    (projectiveLineFlasqueCoefficientPair X n).comp (projectiveLineFlasqueKMap X n) =
      MonoidHom.id ((F X).K n × (F X).K n) := by
  ext ⟨a, b⟩ : 1
  let z := projectiveLineFlasqueKMap X n (a, b)
  have h := projectiveLineFlasqueCoefficientPair_inclusion X n z
  rw [projectiveLineShiftedCoefficientPair_apply, projectiveLineFlasqueKMap_inclusion,
    projectiveLineCorrectedCoordinates_leftInverse] at h
  have hj := (FlasquePerfect.perfectInclusion_KMap_bijective X n).injective
  exact _root_.Prod.ext (hj (congrArg _root_.Prod.fst h)) (hj (congrArg _root_.Prod.snd h))

/-- The other actual composite follows from surjectivity of the same forward functor. -/
theorem projectiveLineFlasqueKMap_comp_coefficientPair [QuasiSeparatedSpace X] (n : ℕ) :
    (projectiveLineFlasqueKMap X n).comp (projectiveLineFlasqueCoefficientPair X n) =
      MonoidHom.id ((F P).K n) := by
  have hsurj : Function.Surjective (projectiveLineFlasqueKMap X n) := by
    intro x
    obtain ⟨⟨a, b⟩, h⟩ :=
      projectiveLineKMap_surjective X n (projectiveLineFlasqueKEquiv X n x)
    have hj := (FlasquePerfect.perfectInclusion_KMap_bijective X n).surjective
    obtain ⟨a, rfl⟩ := hj a
    obtain ⟨b, rfl⟩ := hj b
    refine ⟨(a, b), (projectiveLineFlasqueKEquiv X n).injective ?_⟩
    rw [projectiveLineFlasqueKMap_inclusion, h]
  ext a : 1
  obtain ⟨b, rfl⟩ := hsurj a
  change projectiveLineFlasqueKMap X n
    ((projectiveLineFlasqueCoefficientPair X n).comp (projectiveLineFlasqueKMap X n) b) = _
  rw [projectiveLineFlasqueCoefficientPair_comp]
  rfl

end AlgebraicGeometry.Scheme

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeGlobalInverse.lean:69-117"
  "adaptation" "Both actual chosen-zero K-map composites on termwise flasque perfect complexes"]
  AlgebraicGeometry.Scheme.projectiveLineFlasqueCoefficientPair_comp
  AlgebraicGeometry.Scheme.projectiveLineFlasqueKMap_comp_coefficientPair
