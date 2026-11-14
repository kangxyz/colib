/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalFirstTwistedComparison

/-! # The actual first diagonal coefficient comparison

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

local instance projectiveLineFirstTwistFiniteLocallyFree {Z : Scheme.{u}} (A : Z.Modules)
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

local notation "PB" => Functor.mapHomologicalComplex (pullback p₂) c
local notation "T₋" => BoundedBelowPerfect.tensorVectorBundleRight L
local notation "K₋" => inclusion P ⋙ T₋
local notation "K₀" => inclusion P ⋙ IP
local notation "D" => (inclusion P ⋙ B) ⋙ IQ

/-- The reshuffling isomorphism of the first coefficient, before applying either augmentation. -/
def projectiveLineDiagonalFirstReshuffleIso :
    D ≅ (K₀ ⋙ (LC L)) ⋙ PB ⋙ (LC L₁) :=
  Functor.isoWhiskerLeft K₀ (projectiveLineDiagonalFirstTermReshuffleCochain X)

/-- The morphism underlying the reshuffling isomorphism. -/
def projectiveLineDiagonalFirstReshuffleComparison :
    D ⟶ (K₀ ⋙ (LC L)) ⋙ PB ⋙ (LC L₁) :=
  (projectiveLineDiagonalFirstReshuffleIso X).hom

/-- The right-tensor realization on the second factor, before pulling back. -/
def projectiveLineDiagonalFirstSourceBraiding :
    (K₀ ⋙ (LC L)) ⋙ PB ⋙ (LC L₁) ⟶ K₋ ⋙ IP ⋙ PB ⋙ (LC L₁) :=
  Functor.whiskerLeft K₀
    (Functor.whiskerRight (diagonalTensorBraidingCochain P L).hom (PB ⋙ (LC L₁)))

/-- Pullback and left tensor of the augmentation on the second factor. -/
def projectiveLineDiagonalFirstSourceAugmentation :
    K₋ ⋙ IP ⋙ PB ⋙ (LC L₁) ⟶ S ⋙ IQ ⋙ (LC L₁) :=
  Functor.whiskerRight
    (Functor.whiskerLeft K₋ (unit P)) (U ⋙ IQ ⋙ (LC L₁))

/-- Left tensor of the augmentation on the fibre product. -/
def projectiveLineDiagonalFirstPullbackAugmentation :
    S ⋙ IQ ⋙ (LC L₁) ⟶ H ⋙ IQ ⋙ (LC L₁) :=
  Functor.whiskerRight (Functor.whiskerLeft S (unit Q)) (IQ ⋙ (LC L₁))

/-- The right-tensor realization on the first factor, after resolving the pullback. -/
def projectiveLineDiagonalFirstTargetBraiding :
    H ⋙ IQ ⋙ (LC L₁) ⟶ C ⋙ IQ :=
  Functor.whiskerLeft (H ⋙ IQ) (diagonalTensorBraidingCochain Q L₁).hom

/-- The comparison from the literal first coefficient to the twisted resolved pullback,
before direct image. Both maps into Godement replacements are their actual augmentations. -/
def projectiveLineDiagonalFirstAcyclicComparison :
    inclusion P ⋙ B ⟶ C :=
  let θ : D ⟶ C ⋙ IQ := projectiveLineDiagonalFirstReshuffleComparison X ≫
    projectiveLineDiagonalFirstSourceBraiding X ≫
    projectiveLineDiagonalFirstSourceAugmentation X ≫
    projectiveLineDiagonalFirstPullbackAugmentation X ≫
    projectiveLineDiagonalFirstTargetBraiding X
  { app K := ObjectProperty.homMk (θ.app K)
    naturality {_ _} f := by
      apply ObjectProperty.hom_ext
      exact θ.naturality f }

/-- The map on direct images induced by the first-coefficient comparison. -/
def projectiveLineDiagonalFirstToCommon :
    inclusion P ⋙ V ⟶ projectiveLineDiagonalFirstCommon X :=
  Functor.whiskerRight (projectiveLineDiagonalFirstAcyclicComparison X)
    (total Q ⋙ perfectPushforward p₁)


end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
