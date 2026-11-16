/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalFirstComparisonComponents

/-! # The first coefficient of the diagonal resolution

Resolve the negatively twisted coefficient on the second factor, and resolve
its flat pullback before twisting on the first factor. The invertible twist
preserves acyclicity for the first projection, not necessarily flasqueness.
Consequently the comparisons use actual augmentations throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => CategoryTheory.Limits.pullback π π
local notation "p₁" => CategoryTheory.Limits.pullback.fst π π
local notation "p₂" => CategoryTheory.Limits.pullback.snd π π
local notation "L" => twistOver 1 X (-1)
local notation "L₁" => Functor.obj (pullback p₁) L
local notation "c" => ComplexShape.up ℤ
local notation "IP" => ObjectProperty.ι (BoundedBelowPerfect.objects P)
local notation "IQ" => ObjectProperty.ι (BoundedBelowPerfect.objects Q)
local notation "PerfP" => ObjectProperty.ι
  (IsPerfectComplex (X := LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace P)))
local notation "V" => projectiveLineDiagonalProjectedFirst X
local notation "W" => perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace P))

local instance : IsProper π := isProper_projectiveSpaceOver 1 X
local instance : IsProper p₁ := inferInstance
local instance : Flat p₂ := inferInstance
local instance : Stacks.Ample.IsInvertibleModule Q L₁ :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback p₁ L

local instance projectiveLineFirstFinalTwistFiniteLocallyFree {Z : Scheme.{u}} (A : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z A] :
    SheafOfModules.IsFiniteLocallyFree (R := Z.ringCatSheaf) A :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := Z.ringCatSheaf) A 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Z A
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local notation "J₋" =>
  ((inclusion P ⋙ BoundedBelowPerfect.tensorVectorBundleRight L) ⋙ total P)
local notation "B" => BoundedBelowPerfect.projectiveLineDiagonalBoundedFirst X
local notation "U" => BoundedBelowPerfect.flatPullback p₂
local notation "S" => (J₋ ⋙ inclusion P) ⋙ U
local notation "H" => (S ⋙ total Q) ⋙ inclusion Q
local instance (Z : Scheme.{u}) (M : Z.Modules) :
    (diagonalTwistTensor M).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj Z.sheaf M

local notation "LC" M => Functor.mapHomologicalComplex (diagonalTwistTensor M) c
local notation "R" => BoundedBelowPerfect.tensorVectorBundleRight L₁

local notation "C" => projectiveLineDiagonalFirstAcyclic X

set_option maxHeartbeats 600000 in
-- Compare each actual cochain component separately across the full subcategory.
set_option maxRecDepth 1024 in
/-- The map to the common direct image is a weak equivalence: flat pullback,
invertible tensor and both actual resolutions preserve quasi-isomorphisms. -/
theorem projectiveLineDiagonalFirstToCommon_weak (J : Obj P) :
    (W).weq ((projectiveLineDiagonalFirstToCommon X).app J) := by
  change (W).weq ((perfectPushforward p₁).map
    ((total Q).map ((projectiveLineDiagonalFirstAcyclicComparison X).app J)))
  apply (perfectPushforward_exact p₁).weak
  apply (total_exact Q).weak
  unfold projectiveLineDiagonalFirstAcyclicComparison
  change QuasiIso ((projectiveLineDiagonalFirstReshuffleComparison X).app J ≫
    (projectiveLineDiagonalFirstSourceBraiding X).app J ≫
    (projectiveLineDiagonalFirstSourceAugmentation X).app J ≫
    (projectiveLineDiagonalFirstPullbackAugmentation X).app J ≫
    (projectiveLineDiagonalFirstTargetBraiding X).app J)
  let : QuasiIso ((projectiveLineDiagonalFirstReshuffleComparison X).app J) :=
    projectiveLineDiagonalFirstReshuffleComparison_quasiIso X J
  let : QuasiIso ((projectiveLineDiagonalFirstSourceBraiding X).app J) :=
    projectiveLineDiagonalFirstSourceBraiding_quasiIso X J
  let : QuasiIso ((projectiveLineDiagonalFirstSourceAugmentation X).app J) :=
    projectiveLineDiagonalFirstSourceAugmentation_quasiIso X J
  let : QuasiIso ((projectiveLineDiagonalFirstPullbackAugmentation X).app J) :=
    projectiveLineDiagonalFirstPullbackAugmentation_quasiIso X J
  let : QuasiIso ((projectiveLineDiagonalFirstTargetBraiding X).app J) :=
    projectiveLineDiagonalFirstTargetBraiding_quasiIso X J
  let f₁ := (projectiveLineDiagonalFirstReshuffleComparison X).app J
  let f₂ := (projectiveLineDiagonalFirstSourceBraiding X).app J
  let f₃ := (projectiveLineDiagonalFirstSourceAugmentation X).app J
  let f₄ := (projectiveLineDiagonalFirstPullbackAugmentation X).app J
  let f₅ := (projectiveLineDiagonalFirstTargetBraiding X).app J
  let : QuasiIso (f₄ ≫ f₅) := quasiIso_comp f₄ f₅
  let : QuasiIso (f₃ ≫ f₄ ≫ f₅) := quasiIso_comp f₃ (f₄ ≫ f₅)
  let : QuasiIso (f₂ ≫ f₃ ≫ f₄ ≫ f₅) := quasiIso_comp f₂ (f₃ ≫ f₄ ≫ f₅)
  exact quasiIso_comp f₁ (f₂ ≫ f₃ ≫ f₄ ≫ f₅)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
