/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.EulerBoundedSequence
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectCofibrationSequence
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-! # Euler additivity after genuine derived direct image

All three terms are Godement-resolved before applying ordinary pushforward. These
actual exact functors preserve the pointwise conflation and its arrows, so Waldhausen
additivity computes the signed coefficient on each connective K-group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "S" => projectiveLineEulerSequence X
local notation "V" => BoundedBelowPerfect.waldhausen P
local notation "W" => perfectComplexesWaldhausen X.toRingedSpace
local notation "D" => (total P ⋙ projectiveLineG₀ X)

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local instance : (projectiveLineG₀ X).Additive := by
  unfold projectiveLineG₀
  infer_instance

local notation "E₁" => (_root_.CategoryTheory.ShortComplex.X₁ (projectiveLineEulerSequence X))
local notation "E₂" => (_root_.CategoryTheory.ShortComplex.X₂ (projectiveLineEulerSequence X))
local notation "E₃" => (_root_.CategoryTheory.ShortComplex.X₃ (projectiveLineEulerSequence X))

/-- Godement totalization and direct image preserve the Euler inclusion. -/
def projectiveLineEulerProjectedFirst :
    (BoundedBelowPerfect.tensorVectorBundleRight E₁ ⋙ D) ⟶
      (BoundedBelowPerfect.tensorVectorBundleRight E₂ ⋙ D) :=
  Functor.whiskerRight (BoundedBelowPerfect.tensorVectorBundleRightMap (S).f) D

/-- Godement totalization and direct image preserve the Euler quotient. -/
def projectiveLineEulerProjectedSecond :
    (BoundedBelowPerfect.tensorVectorBundleRight E₂ ⋙ D) ⟶
      (BoundedBelowPerfect.tensorVectorBundleRight E₃ ⋙ D) :=
  Functor.whiskerRight (BoundedBelowPerfect.tensorVectorBundleRightMap (S).g) D

theorem projectiveLineEulerProjected_comp_zero :
    projectiveLineEulerProjectedFirst X ≫ projectiveLineEulerProjectedSecond X = 0 := by
  apply NatTrans.ext
  funext K
  change (D).map _ ≫ (D).map _ = 0
  have h := NatTrans.congr_app
    (BoundedBelowPerfect.tensorVectorBundleRightMap_comp_eq_zero (S).zero) K
  change (BoundedBelowPerfect.tensorVectorBundleRightMap (S).f).app K ≫
    (BoundedBelowPerfect.tensorVectorBundleRightMap (S).g).app K = 0 at h
  rw [← Functor.map_comp, h, Functor.map_zero]

/-- The literal Godement-resolved Euler sequence stays short exact after direct image. -/
theorem projectiveLineEulerProjected_shortExact (K : BoundedBelowPerfect.Obj P) :
    (((BoundedBelowPerfect.projectiveLineEulerBoundedSequence X K).map D).map
      (ObjectProperty.ι (IsPerfectComplex (X := X.toRingedSpace)))).ShortExact := by
  let U := BoundedBelowPerfect.projectiveLineEulerBoundedSequence X K
  change ((U.map (total P ⋙ projectiveLineG₀ X)).map _).ShortExact
  rw [ShortComplex.map_comp]
  have hT : ((U.map (total P)).map (objects P).ι).ShortExact :=
    BoundedBelowPerfect.godementTotal_shortExact
      (BoundedBelowPerfect.projectiveLineEulerBoundedSequence_shortExact X K)
  exact perfectPushforward_shortExact π hT

/-- The actual projective-line Euler sequence yields the coefficient cofibration sequence. -/
theorem projectiveLineEulerProjected_isCofibrationSequence :
    Additivity.IsCofibrationSequence V W
      (projectiveLineEulerProjectedFirst X) (projectiveLineEulerProjectedSecond X) := by
  let e := (total_exact P).comp (projectiveLineG₀_exact X)
  apply perfectCofibrationSequence_of_shortExact V X.toRingedSpace _ _
    (projectiveLineEulerProjected_comp_zero X)
    ((BoundedBelowPerfect.tensorVectorBundleRight_exact E₁).comp e)
    ((BoundedBelowPerfect.tensorVectorBundleRight_exact E₂).comp e)
    ((BoundedBelowPerfect.tensorVectorBundleRight_exact E₃).comp e)
  intro K
  have h := projectiveLineEulerProjected_shortExact X K
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])) h

/-- The signed coefficient relation, before identifying each of the three terms. -/
theorem projectiveLineEulerProjected_additivity (n : ℕ) (x : (V).K n) :
    KMap ((BoundedBelowPerfect.tensorVectorBundleRight_exact
      (projectiveLineEulerSequence X).X₂).comp
        ((total_exact P).comp (projectiveLineG₀_exact X))) n x =
      KMap ((BoundedBelowPerfect.tensorVectorBundleRight_exact
        (projectiveLineEulerSequence X).X₁).comp
          ((total_exact P).comp (projectiveLineG₀_exact X))) n x *
      KMap ((BoundedBelowPerfect.tensorVectorBundleRight_exact
        (projectiveLineEulerSequence X).X₃).comp
          ((total_exact P).comp (projectiveLineG₀_exact X))) n x := by
  let : HasBinaryCoproducts _ := Additivity.hasBinaryCoproducts W
  exact Additivity.KMap_additivity_mul V W _ _
    (projectiveLineEulerProjected_isCofibrationSequence X)
    n x

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
