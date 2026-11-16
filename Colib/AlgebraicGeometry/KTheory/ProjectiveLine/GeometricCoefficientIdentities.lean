/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricInverse
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.NegativeCoefficientVanishing
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PositiveResolvedUnit
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwoSummands

/-! # The coefficient maps on the two canonical projective-line summands

The literal bounded-below inclusion is surjective on K-groups. For a bounded-below
representative, one may compute either coefficient on the actual Godement total of
the corresponding summand, using its augmentation as a weak natural comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [CompactSpace X]

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "L" => twistOver 1 X (-1)
local notation "W" Y =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

local instance :
    SheafOfModules.IsFiniteLocallyFree (R := (P).ringCatSheaf) L :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local notation "I" Y => (BoundedBelowPerfect.inclusion Y)
local notation "i" Y => BoundedBelowPerfect.inclusion_exact Y
local notation "U" => FlasquePerfect.total P
local notation "uE" => FlasquePerfect.total_exact P
local notation "J" => FlasquePerfect.perfectInclusion P
local notation "j" => FlasquePerfect.perfectInclusion_exact P
local notation "A₀" => BoundedBelowPerfect.flatPullback π
local notation "a₀" => BoundedBelowPerfect.flatPullback_exact π
local notation "T₁" => BoundedBelowPerfect.tensorVectorBundleRight L
local notation "t₁" => BoundedBelowPerfect.tensorVectorBundleRight_exact L

/-- A summand on a bounded-below representative agrees on K-groups with its resolved lift. -/
theorem projectiveLineKMap_summand_on_boundedBelow
    {A : BoundedBelowPerfect.Obj X ⥤ BoundedBelowPerfect.Obj P}
    (a : IsExact (BoundedBelowPerfect.waldhausen X).cof
      (BoundedBelowPerfect.waldhausen X).weq (BoundedBelowPerfect.waldhausen P).cof
      (BoundedBelowPerfect.waldhausen P).weq A)
    {F : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace)) ⥤
      ObjectProperty.FullSubcategory (IsPerfectComplex (X := (P).toRingedSpace))}
    (f : IsExact (W X).cof (W X).weq (W P).cof (W P).weq F)
    (e : A ⋙ (I P) ≅ (I X) ⋙ F) (n : ℕ) (x : (BoundedBelowPerfect.waldhausen X).K n) :
    KMap f n (KMap (i X) n x) =
      projectiveLineFlasqueKEquiv X n (KMap (a.comp uE) n x) := by
  let η : A ⋙ (I P) ⟶ (A ⋙ U) ⋙ J :=
    Functor.whiskerLeft A (Functor.whiskerRight (FlasquePerfect.unit P) (I P))
  have hη (K : BoundedBelowPerfect.Obj X) : (W P).weq (η.app K) :=
    (i P).weak _ (FlasquePerfect.unit_weak P (A.obj K))
  have he := KMap_eq_of_iso (a.comp (i P)) ((i X).comp f) e n
  have hw := KMap_eq_of_weakNatTrans (a.comp (i P)) ((a.comp uE).comp j) η hη n
  change KMap f n (KMap (i X) n x) = KMap j n (KMap (a.comp uE) n x)
  calc
    _ = KMap ((i X).comp f) n x :=
      DFunLike.congr_fun (KMap_comp_KMap (i X) f n) x
    _ = KMap (a.comp (i P)) n x := DFunLike.congr_fun he.symm x
    _ = KMap ((a.comp uE).comp j) n x := DFunLike.congr_fun hw x
    _ = _ := DFunLike.congr_fun (KMap_comp_KMap (a.comp uE) j n).symm x

/-- The lifted negative summand agrees with the canonical one by the chain braiding. -/
def projectiveLineSecondSummandInclusionIso :
    (A₀ ⋙ T₁) ⋙ (I P) ≅ (I X) ⋙ projectiveLineSecondSummand X :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (BoundedBelowPerfect.tensorVectorBundleRightInclusionIso L) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (BoundedBelowPerfect.flatPullbackInclusionIso π) _ ≪≫
    Functor.associator _ _ _

/-- The two actual coefficients of the untwisted summand are the input and the unit. -/
theorem projectiveLineGeometricKMap_firstSummand (n : ℕ) (x : (W X).K n) :
    projectiveLineGeometricKMap X n (KMap (projectiveLineFirstSummand_exact X) n x) = (x, 1) := by
  obtain ⟨y, rfl⟩ := (BoundedBelowPerfect.inclusion_KMap_bijective X n).surjective x
  rw [projectiveLineKMap_summand_on_boundedBelow X a₀ (projectiveLineFirstSummand_exact X)
    (BoundedBelowPerfect.flatPullbackInclusionIso π) n y,
    projectiveLineGeometricKMap_of_flasque]
  let g₀ := FlasquePerfect.projectiveLineG₀_exact X
  let g₁ := FlasquePerfect.projectiveLineG₁_exact X
  refine _root_.Prod.ext ?_ ?_
  · change KMap g₀ n (KMap ((a₀).comp uE) n y) = KMap (i X) n y
    exact (DFunLike.congr_fun (KMap_comp_KMap ((a₀).comp uE) g₀ n) y).trans
      (DFunLike.congr_fun (FlasquePerfect.projectiveLineG₀_untwisted_KMap X n) y)
  · change KMap g₁ n (KMap ((a₀).comp uE) n y) = 1
    exact (DFunLike.congr_fun (KMap_comp_KMap ((a₀).comp uE) g₁ n) y).trans
      (DFunLike.congr_fun (FlasquePerfect.projectiveLineG₁_untwisted_KMap X n) y)

/-- The untwisted coefficient of the negative summand is the unit. -/
theorem projectiveLineGeometricKMap_secondSummand_fst (n : ℕ) (x : (W X).K n) :
    (projectiveLineGeometricKMap X n (KMap (projectiveLineSecondSummand_exact X) n x)).1 = 1 := by
  obtain ⟨y, rfl⟩ := (BoundedBelowPerfect.inclusion_KMap_bijective X n).surjective x
  rw [projectiveLineKMap_summand_on_boundedBelow X ((a₀).comp t₁)
    (projectiveLineSecondSummand_exact X) (projectiveLineSecondSummandInclusionIso X) n y,
    projectiveLineGeometricKMap_of_flasque]
  let g₀ := FlasquePerfect.projectiveLineG₀_exact X
  change KMap g₀ n (KMap (((a₀).comp t₁).comp uE) n y) = 1
  exact (DFunLike.congr_fun (KMap_comp_KMap (((a₀).comp t₁).comp uE) g₀ n) y).trans
    (DFunLike.congr_fun (FlasquePerfect.projectiveLineG₀_negative_KMap X n) y)

end AlgebraicGeometry.Scheme
