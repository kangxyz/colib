/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.EulerProjectedSequence
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.EulerMiddleComparison
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.NegativeCoefficientVanishing
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PositiveResolvedUnit

/-! # The signed second coefficient

The projected Euler sequence for the two coordinate sections computes the coefficient of
the negative summand. Its middle term vanishes and its last term is the positive coefficient.
The addition identity uses the actual arrows, rather than an objectwise choice of representatives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "W" => perfectComplexesWaldhausen X.toRingedSpace
local notation "U" => BoundedBelowPerfect.waldhausen X
local notation "S" => projectiveLineEulerSequence X

local instance eulerSignProjectiveProper : IsProper π := isProper_projectiveSpaceOver 1 X

local notation "E₁" => (_root_.CategoryTheory.ShortComplex.X₁ (projectiveLineEulerSequence X))
local notation "E₂" => (_root_.CategoryTheory.ShortComplex.X₂ (projectiveLineEulerSequence X))
local notation "E₃" => (_root_.CategoryTheory.ShortComplex.X₃ (projectiveLineEulerSequence X))

local notation "A" => BoundedBelowPerfect.flatPullback_exact π
local notation "t" E => (BoundedBelowPerfect.tensorVectorBundleRight_exact E)
local notation "D" => (IsExact.comp (total_exact P) (projectiveLineG₀_exact X))

local instance eulerSignTensorMonoidal : MonoidalCategory (P).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (P).sheaf

local instance eulerSignTensorPreadditive : MonoidalPreadditive (P).Modules := by
  let := Abelian.hasFiniteBiproducts (C := (P).Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor (P).sheaf

local notation "L" => (twistOver 1 X (-1))

local instance eulerSignTwistFiniteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local notation "T" => BoundedBelowPerfect.tensorVectorBundleRight L

/-- Two applications of the negative twist agree with the first Euler term. -/
def projectiveLineEulerFirstTensorIso :
    T ⋙ T ≅ BoundedBelowPerfect.tensorVectorBundleRight E₁ :=
  BoundedBelowPerfect.tensorVectorBundleRightTensorIso
    (twistOverMulIso 1 X (-1) (-1) ≪≫ (projectiveLineEulerFirstIso X).symm)

/-- Applying the first resolution in the geometric second coefficient does not change its K-map. -/
theorem projectiveLineG₁_resolved_KMap_apply (n : ℕ)
    (x : (BoundedBelowPerfect.waldhausen P).K n) :
    KMap (projectiveLineG₁_exact X) n (KMap (total_exact P) n x) =
      KMap ((t L).comp D) n x := by
  let e := (t L).comp D
  let h := (total_exact P).comp (projectiveLineG₁_exact X)
  let F := T ⋙ (total P ⋙ projectiveLineG₀ X)
  let η : F ⟶ total P ⋙ projectiveLineG₁ X :=
    (Functor.leftUnitor F).inv ≫ Functor.whiskerRight (unit P) F
  have hη (K : BoundedBelowPerfect.Obj P) : (W).weq (η.app K) :=
    e.weak ((unit P).app K) (unit_weak P K)
  have q := KMap_eq_of_weakNatTrans e h η hη n
  exact (DFunLike.congr_fun (KMap_comp_KMap (total_exact P) (projectiveLineG₁_exact X) n)
    x).trans (DFunLike.congr_fun q.symm x)

/-- The last Euler term acts by the identity before taking direct image. -/
def projectiveLineEulerLastTensorIso :
    BoundedBelowPerfect.tensorVectorBundleRight E₃ ≅ 𝟭 (BoundedBelowPerfect.Obj P) :=
  BoundedBelowPerfect.tensorVectorBundleRightUnitIso (projectiveLineEulerLastIso X)

/-- The last projected coefficient is the positive coefficient on the original input. -/
theorem projectiveLineEulerLast_KMap_apply (n : ℕ) (x : (U).K n) :
    KMap ((t E₃).comp D) n (KMap A n x) =
      KMap (BoundedBelowPerfect.inclusion_exact X) n x := by
  let e := Functor.isoWhiskerRight (projectiveLineEulerLastTensorIso X)
    (total P ⋙ projectiveLineG₀ X) ≪≫ Functor.leftUnitor _
  have hh := KMap_eq_of_iso ((t E₃).comp D) D e n
  rw [hh]
  calc
    _ = KMap ((A).comp D) n x := DFunLike.congr_fun (KMap_comp_KMap A D n) x
    _ = KMap ((((A).comp (total_exact P)).comp (projectiveLineG₀_exact X))) n x := rfl
    _ = _ := DFunLike.congr_fun (projectiveLineG₀_untwisted_KMap X n) x

/-- The projected Euler conflation determines the first term from the other two. -/
theorem projectiveLineEulerFirst_KMap_apply_of_middle_and_last (n : ℕ) (x : (U).K n)
    (hMiddle : KMap ((t E₂).comp D) n (KMap A n x) = 1)
    (hLast : KMap ((t E₃).comp D) n (KMap A n x) =
      KMap (BoundedBelowPerfect.inclusion_exact X) n x) :
    KMap ((t E₁).comp D) n (KMap A n x) =
      (KMap (BoundedBelowPerfect.inclusion_exact X) n x)⁻¹ := by
  have h := projectiveLineEulerProjected_additivity X n (KMap A n x)
  rw [hMiddle, hLast] at h
  calc
    _ = (KMap ((t E₁).comp D) n (KMap A n x) *
        KMap (BoundedBelowPerfect.inclusion_exact X) n x) *
        (KMap (BoundedBelowPerfect.inclusion_exact X) n x)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := by rw [← h, one_mul]

/-- The middle coefficient is trivial on the flat pullback of an input complex. -/
theorem projectiveLineEulerMiddle_KMap_apply (n : ℕ) (x : (U).K n) :
    KMap ((t E₂).comp D) n (KMap A n x) = 1 := by
  rw [projectiveLineEulerMiddle_KMap]
  have h := projectiveLineG₁_resolved_KMap_apply X n (KMap A n x)
  rw [← h]
  have h' := DFunLike.congr_fun (projectiveLineG₁_untwisted_KMap X n) x
  rw [← KMap_comp_KMap ((A).comp (total_exact P)) (projectiveLineG₁_exact X) n,
    MonoidHom.comp_apply, ← KMap_comp_KMap (A) (total_exact P) n] at h'
  change KMap (projectiveLineG₁_exact X) n (KMap (total_exact P) n (KMap A n x)) = 1 at h'
  rw [h', one_pow]

/-- The first projected coefficient of the Euler sequence gives the negative sign. -/
theorem projectiveLineEulerFirst_KMap_apply (n : ℕ) (x : (U).K n) :
    KMap ((t E₁).comp D) n (KMap A n x) =
      (KMap (BoundedBelowPerfect.inclusion_exact X) n x)⁻¹ :=
  projectiveLineEulerFirst_KMap_apply_of_middle_and_last X n x
    (projectiveLineEulerMiddle_KMap_apply X n x) (projectiveLineEulerLast_KMap_apply X n x)

/-- The actual doubly twisted coefficient on the flat pullback has the Euler sign. -/
theorem projectiveLineG₁_negative_KMap_apply (n : ℕ) (x : (U).K n) :
    KMap (projectiveLineG₁_exact X) n
      (KMap (total_exact P) n (KMap (t L) n (KMap A n x))) =
      (KMap (BoundedBelowPerfect.inclusion_exact X) n x)⁻¹ := by
  rw [projectiveLineG₁_resolved_KMap_apply]
  have h := DFunLike.congr_fun (KMap_comp_KMap (t L) ((t L).comp D) n) (KMap A n x)
  let e := (Functor.associator T T _).symm ≪≫
    Functor.isoWhiskerRight (projectiveLineEulerFirstTensorIso X)
      (total P ⋙ projectiveLineG₀ X)
  have h' := DFunLike.congr_fun (KMap_eq_of_iso ((t L).comp ((t L).comp D))
    ((t E₁).comp D) e n) (KMap A n x)
  exact h.trans (h'.trans (projectiveLineEulerFirst_KMap_apply X n x))

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
