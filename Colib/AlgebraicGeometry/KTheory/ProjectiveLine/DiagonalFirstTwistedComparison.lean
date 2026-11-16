/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalMiddleComparison
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalTwistedPushforward
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorFirstTerm

/-! # The twisted projective direct image of the first diagonal coefficient

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

local instance projectiveLineTwistFiniteLocallyFree {Z : Scheme.{u}} (A : Z.Modules)
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

/-- The right-tensor realization of the first-factor twist of the resolved pullback. -/
def projectiveLineDiagonalFirstAcyclic : Obj P ⥤ BoundedBelowPerfect.Obj Q :=
  H ⋙ R

local notation "C" => projectiveLineDiagonalFirstAcyclic X

/-- The projective image of the Godement resolution of the acyclic first coefficient. -/
def projectiveLineDiagonalFirstCommon :=
  (C ⋙ total Q) ⋙ perfectPushforward p₁

/-- The intervening functor is exact, since each of resolution, pullback, invertible
tensor, and direct image on the flasque representatives is exact. -/
theorem projectiveLineDiagonalFirstCommon_exact :
    Waldhausen.IsExact (waldhausen P).cof (waldhausen P).weq (W).cof (W).weq
      (projectiveLineDiagonalFirstCommon X) :=
  (((((((((inclusion_exact P).comp
    (BoundedBelowPerfect.tensorVectorBundleRight_exact L)).comp (total_exact P)).comp
    (inclusion_exact P)).comp (BoundedBelowPerfect.flatPullback_exact p₂)).comp
    (total_exact Q)).comp (inclusion_exact Q)).comp
    (BoundedBelowPerfect.tensorVectorBundleRight_exact L₁)).comp (total_exact Q)).comp
    (perfectPushforward_exact p₁)

local instance (Z : Scheme.{u}) (M : Z.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj M)
      |>.PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorFlipObj Z.sheaf M

/-- The native sheaf tensor braiding on actual cochain complexes. -/
def diagonalTensorBraidingCochain (Z : Scheme.{u}) (M : Z.Modules) :
    (LC M) ≅
      Functor.mapHomologicalComplex
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj M) c :=
  NatIso.mapHomologicalComplex
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u, u, u} Z.sheaf).app M) c

local notation "F" => Functor.mapHomologicalComplex (pushforward p₁) c
local notation "PBC" => projectiveLineDiagonalBaseChangeCochain X

local notation "Jc" => J₋ ⋙ inclusion P ⋙ IP
local notation "G₋" => (projectiveLineG₁ X ⋙ perfectFlatPullback π) ⋙ perfectTensorLeft L
local notation "P₂c" => Functor.mapHomologicalComplex (pullback p₂) c

/-- Base change on the resolved coefficient, before applying the projection formula. -/
def projectiveLineDiagonalTwistedBaseChange :
    G₋ ⋙ PerfP ⟶ S ⋙ IQ ⋙ F ⋙ (LC L) :=
  Functor.whiskerLeft Jc (Functor.whiskerRight PBC (LC L))

/-- Direct image of the augmentation of the pulled-back coefficient. -/
def projectiveLineDiagonalTwistedPullbackAugmentation :
    S ⋙ IQ ⋙ F ⋙ (LC L) ⟶ H ⋙ IQ ⋙ F ⋙ (LC L) :=
  Functor.whiskerRight (Functor.whiskerLeft S (unit Q)) (IQ ⋙ F ⋙ (LC L))

/-- The degreewise invertible projection formula on the resolved coefficient. -/
def projectiveLineDiagonalTwistedProjectionFormula :
    H ⋙ IQ ⋙ F ⋙ (LC L) ⟶ H ⋙ IQ ⋙ (LC L₁) ⋙ F :=
  Functor.whiskerLeft (H ⋙ IQ) (pushforwardTensorLeftInvertibleCochainIso p₁ L).inv

/-- The braiding in the ordinary direct image on the fibre product. -/
def projectiveLineDiagonalTwistedTargetBraiding :
    H ⋙ IQ ⋙ (LC L₁) ⋙ F ⟶ C ⋙ IQ ⋙ F :=
  Functor.whiskerLeft (H ⋙ IQ)
    (Functor.whiskerRight (diagonalTensorBraidingCochain Q L₁).hom F)

/-- Direct image of the actual augmentation of the twisted coefficient. -/
def projectiveLineDiagonalTwistedTargetAugmentation :
    C ⋙ IQ ⋙ F ⟶ projectiveLineDiagonalFirstCommon X ⋙ PerfP :=
  Functor.whiskerRight (Functor.whiskerLeft C (unit Q)) (IQ ⋙ F)

/-- The comparison into the common direct image from the geometric twisted coefficient:
apply the base-change mate, use the projection formula, then apply the pushed
Godement augmentation. -/
def projectiveLineDiagonalTwistedToCommon :
    G₋ ⟶ projectiveLineDiagonalFirstCommon X :=
  let θ := projectiveLineDiagonalTwistedBaseChange X ≫
    projectiveLineDiagonalTwistedPullbackAugmentation X ≫
    projectiveLineDiagonalTwistedProjectionFormula X ≫
    projectiveLineDiagonalTwistedTargetBraiding X ≫
    projectiveLineDiagonalTwistedTargetAugmentation X
  { app J := ObjectProperty.homMk (θ.app J)
    naturality {_ _} f := by
      apply ObjectProperty.hom_ext
      exact θ.naturality f }

set_option maxHeartbeats 600000 in
-- Each component is compared at a literal cochain representative.
set_option maxRecDepth 1024 in
/-- The geometric twisted comparison is a weak equivalence: the actual
flat base-change map is followed by the projection formula, and the
pushed augmentation is a quasi-isomorphism by right acyclicity. -/
theorem projectiveLineDiagonalTwistedToCommon_weak (J : Obj P) :
    (W).weq ((projectiveLineDiagonalTwistedToCommon X).app J) := by
  let K := (J₋).obj J
  let U₀ := (S).obj J
  let H₀ := (total Q).obj U₀
  let a := ((unit Q).app U₀).hom
  have : QuasiIso a := unit_weak Q U₀
  let β := (PBC).app K.obj ≫ (F).map a
  have hβ : QuasiIso β := projectiveLineDiagonalBaseChangeCochain_comp_quasiIso X
    K.obj H₀.obj K.property.1.1 K.property.1.2 H₀.property.1.2
    K.property.2 H₀.property.2 a
  have htβ : QuasiIso ((LC L).map β) :=
    (perfectTensorLeft_waldhausenExact L).weak
      (X := ((projectiveLineG₁ X ⋙ perfectFlatPullback π).obj J))
      (Y := (perfectPushforward p₁).obj H₀) (ObjectProperty.homMk β) hβ
  let r := (diagonalTensorBraidingCochain Q L₁).hom.app H₀.obj
  let C₀ := (C).obj J
  let b := ((unit Q).app C₀).hom
  have : QuasiIso b := unit_weak Q C₀
  have : QuasiIso (r ≫ b) := inferInstance
  have hrb : QuasiIso ((F).map (r ≫ b)) :=
    quasiIso_pushforward_tensorLeftPullbackInvertible_resolution p₁ L (r ≫ b)
      (ObjectProperty.prop_of_iso (CochainComplex.plus (Q).Modules)
        ((diagonalTensorBraidingCochain Q L₁).app H₀.obj).symm
        C₀.property.2)
      ((total Q).obj C₀).property.1.2
      (fun n => pushforward_rightAcyclic_of_flasque p₁ _ (H₀.property.2 n))
      ((total Q).obj C₀).property.2
  unfold projectiveLineDiagonalTwistedToCommon
  change QuasiIso (((projectiveLineDiagonalTwistedBaseChange X).app J) ≫
    (projectiveLineDiagonalTwistedPullbackAugmentation X).app J ≫
    (projectiveLineDiagonalTwistedProjectionFormula X).app J ≫
    (projectiveLineDiagonalTwistedTargetBraiding X).app J ≫
    (projectiveLineDiagonalTwistedTargetAugmentation X).app J)
  have h₁ : (projectiveLineDiagonalTwistedBaseChange X).app J =
      (LC L).map ((PBC).app K.obj) := rfl
  have h₂ : (projectiveLineDiagonalTwistedPullbackAugmentation X).app J =
      (LC L).map ((F).map a) := rfl
  have h₃ : (projectiveLineDiagonalTwistedProjectionFormula X).app J =
      (pushforwardTensorLeftInvertibleCochainIso p₁ L).inv.app H₀.obj := rfl
  have h₄ : (projectiveLineDiagonalTwistedTargetBraiding X).app J = (F).map r := rfl
  have h₅ : (projectiveLineDiagonalTwistedTargetAugmentation X).app J = (F).map b := rfl
  rw [h₁, h₂, h₃, h₄, h₅]
  have h : QuasiIso ((LC L).map β ≫
      (pushforwardTensorLeftInvertibleCochainIso p₁ L).inv.app H₀.obj ≫
      (F).map (r ≫ b)) := inferInstance
  simpa only [β, Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
