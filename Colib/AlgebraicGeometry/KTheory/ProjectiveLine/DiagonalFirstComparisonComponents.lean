/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalFirstAcyclicComparison

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

local instance projectiveLineFirstWeakTwistFiniteLocallyFree {Z : Scheme.{u}} (A : Z.Modules)
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

/-- The reshuffling stage of the first-coefficient map is a quasi-isomorphism. -/
theorem projectiveLineDiagonalFirstReshuffleComparison_quasiIso (J : Obj P) :
    QuasiIso ((projectiveLineDiagonalFirstReshuffleComparison X).app J) :=
  quasiIso_of_isIso ((projectiveLineDiagonalFirstReshuffleIso X).app J).hom

/-- The SourceBraiding stage of the first-coefficient map is a quasi-isomorphism. -/
theorem projectiveLineDiagonalFirstSourceBraiding_quasiIso (J : Obj P) :
    QuasiIso ((projectiveLineDiagonalFirstSourceBraiding X).app J) := by
  let l := (Functor.whiskerRight (diagonalTensorBraidingCochain P L).hom
    ((pullback p₂).mapHomologicalComplex c ⋙ (LC L₁))).app J.obj
  have hl : QuasiIso l := inferInstance
  have h : (projectiveLineDiagonalFirstSourceBraiding X).app J = l := rfl
  exact h.symm ▸ hl

/-- The SourceAugmentation stage of the first-coefficient map is a quasi-isomorphism. -/
theorem projectiveLineDiagonalFirstSourceAugmentation_quasiIso (J : Obj P) :
    QuasiIso ((projectiveLineDiagonalFirstSourceAugmentation X).app J) := by
  let Jt := (inclusion P ⋙ BoundedBelowPerfect.tensorVectorBundleRight L).obj J
  let a := ((U).map ((unit P).app Jt)).hom
  have ha : QuasiIso a :=
    (BoundedBelowPerfect.flatPullback_exact p₂).weak _ (unit_weak P Jt)
  have hta : QuasiIso ((LC L₁).map a) :=
    (perfectTensorLeft_waldhausenExact L₁).weak
      ((BoundedBelowPerfect.inclusion Q).map ((U).map ((unit P).app Jt))) ha
  have h : (projectiveLineDiagonalFirstSourceAugmentation X).app J = (LC L₁).map a := rfl
  exact h.symm ▸ hta

/-- The PullbackAugmentation stage of the first-coefficient map is a quasi-isomorphism. -/
theorem projectiveLineDiagonalFirstPullbackAugmentation_quasiIso (J : Obj P) :
    QuasiIso ((projectiveLineDiagonalFirstPullbackAugmentation X).app J) := by
  let S₀ := (S).obj J
  let b := ((unit Q).app S₀).hom
  have hb : QuasiIso b := unit_weak Q S₀
  have htb : QuasiIso ((LC L₁).map b) :=
    (perfectTensorLeft_waldhausenExact L₁).weak
      ((BoundedBelowPerfect.inclusion Q).map ((unit Q).app S₀)) hb
  have h : (projectiveLineDiagonalFirstPullbackAugmentation X).app J = (LC L₁).map b := rfl
  exact h.symm ▸ htb

/-- The TargetBraiding stage of the first-coefficient map is a quasi-isomorphism. -/
theorem projectiveLineDiagonalFirstTargetBraiding_quasiIso (J : Obj P) :
    QuasiIso ((projectiveLineDiagonalFirstTargetBraiding X).app J) := by
  let r := (diagonalTensorBraidingCochain Q L₁).hom.app ((H).obj J).obj
  have hr : QuasiIso r := inferInstance
  have h : (projectiveLineDiagonalFirstTargetBraiding X).app J = r := rfl
  exact h.symm ▸ hr

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
