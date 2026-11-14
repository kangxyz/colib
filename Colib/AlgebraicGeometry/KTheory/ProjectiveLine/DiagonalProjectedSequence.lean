/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalBoundedSequence
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.CoefficientFunctors
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectCofibrationSequence
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-! # Derived direct image of the diagonal resolution

Resolve the actual three coefficient complexes by their functorial Godement totals,
then push them forward along the first projection. The inherited conflations give
Waldhausen additivity with the literal diagonal arrows.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => Limits.pullback π π
local notation "p₁" => Limits.pullback.fst π π
local notation "V" => BoundedBelowPerfect.waldhausen P
local notation "W" => perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace P))

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local notation "D" => (total Q ⋙ perfectPushforward p₁)

open BoundedBelowPerfect in
/-- The derived direct image of the first diagonal coefficient. -/
def projectiveLineDiagonalProjectedFirst := projectiveLineDiagonalBoundedFirst X ⋙ D

open BoundedBelowPerfect in
/-- The derived direct image of the middle diagonal coefficient. -/
def projectiveLineDiagonalProjectedMiddle := projectiveLineDiagonalBoundedMiddle X ⋙ D

open BoundedBelowPerfect in
/-- The derived direct image of the diagonal-supported coefficient. -/
def projectiveLineDiagonalProjectedLast := projectiveLineDiagonalBoundedLast X ⋙ D

open BoundedBelowPerfect in
/-- The actual diagonal inclusion after resolution and pushforward. -/
def projectiveLineDiagonalProjectedInclusion :
    projectiveLineDiagonalProjectedFirst X ⟶ projectiveLineDiagonalProjectedMiddle X :=
  Functor.whiskerRight (projectiveLineDiagonalBoundedInclusion X) D

open BoundedBelowPerfect in
/-- The actual diagonal quotient after resolution and pushforward. -/
def projectiveLineDiagonalProjectedQuotient :
    projectiveLineDiagonalProjectedMiddle X ⟶ projectiveLineDiagonalProjectedLast X :=
  Functor.whiskerRight (projectiveLineDiagonalBoundedQuotient X) D

open BoundedBelowPerfect in
theorem projectiveLineDiagonalProjected_comp_zero :
    projectiveLineDiagonalProjectedInclusion X ≫
      projectiveLineDiagonalProjectedQuotient X = 0 := by
  apply NatTrans.ext
  funext K
  change (D).map _ ≫ (D).map _ = 0
  have h := NatTrans.congr_app (projectiveLineDiagonalBounded_comp_zero X) K
  change (projectiveLineDiagonalBoundedInclusion X).app K ≫
    (projectiveLineDiagonalBoundedQuotient X).app K = 0 at h
  rw [← Functor.map_comp, h, Functor.map_zero]

local notation "e" => (IsExact.comp (total_exact Q) (perfectPushforward_exact p₁))

open BoundedBelowPerfect in
/-- The literal Godement-resolved diagonal sequence stays short exact after direct image. -/
theorem projectiveLineDiagonalProjected_shortExact (K : BoundedBelowPerfect.Obj P) :
    (((projectiveLineDiagonalBoundedSequence X K).map D).map
      (ObjectProperty.ι (IsPerfectComplex (X := (P).toRingedSpace)))).ShortExact := by
  let U := projectiveLineDiagonalBoundedSequence X K
  change ((U.map (total Q ⋙ perfectPushforward p₁)).map _).ShortExact
  rw [ShortComplex.map_comp]
  have hT : ((U.map (total Q)).map (objects Q).ι).ShortExact :=
    BoundedBelowPerfect.godementTotal_shortExact
      (projectiveLineDiagonalBoundedSequence_shortExact X K)
  exact perfectPushforward_shortExact p₁ hT

open BoundedBelowPerfect in
/-- Direct image of the actual resolved diagonal sequence is a cofibration sequence. -/
theorem projectiveLineDiagonalProjected_isCofibrationSequence :
    Additivity.IsCofibrationSequence V W
      (projectiveLineDiagonalProjectedInclusion X) (projectiveLineDiagonalProjectedQuotient X) := by
  apply perfectCofibrationSequence_of_shortExact V (P).toRingedSpace _ _
    (projectiveLineDiagonalProjected_comp_zero X)
    ((projectiveLineDiagonalBoundedFirst_exact X).comp e)
    ((projectiveLineDiagonalBoundedMiddle_exact X).comp e)
    ((projectiveLineDiagonalBoundedLast_exact X).comp e)
  intro K
  have h := projectiveLineDiagonalProjected_shortExact X K
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])) h

open BoundedBelowPerfect in
/-- The three actual terms of the diagonal resolution give the additivity relation. -/
theorem projectiveLineDiagonalProjected_KMap_additivity (n : ℕ) (x : (V).K n) :
    KMap ((projectiveLineDiagonalBoundedMiddle_exact X).comp e) n x =
      KMap ((projectiveLineDiagonalBoundedFirst_exact X).comp e) n x *
      KMap ((projectiveLineDiagonalBoundedLast_exact X).comp e) n x := by
  let : HasBinaryCoproducts _ := Additivity.hasBinaryCoproducts W
  exact Additivity.KMap_additivity_mul V W _ _
    (projectiveLineDiagonalProjected_isCofibrationSequence X) n x

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
