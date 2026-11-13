/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowPullback
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.NegativeDerivedCoefficient

/-! # The mixed projective-line coefficient is acyclic

For a perfect complex `K` on the base, the actual direct image of the Godement resolution of
`𝒪(-1) ⊗ π* K` represents zero. The projection formula applies to the actual flat pullback
and the degree-zero negative twist, whose derived direct image vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

attribute [local instance 2000] HasDerivedCategory.standard

variable (X : Scheme.{u})

local notation "P" => (projectiveSpaceOver 1 X)
local notation "π" => (P ↘ X)
local notation "L" => (twistOver 1 X (-1))
local notation "c" => ComplexShape.up ℤ

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local instance : SheafOfModules.IsFiniteLocallyFree (R := (P).ringCatSheaf) L :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local instance coefficientTensorMonoidal : MonoidalCategory (P).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (P).sheaf

local instance coefficientTensorAdditive : MonoidalPreadditive (P).Modules := by
  let := Abelian.hasFiniteBiproducts (C := (P).Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor (P).sheaf

local instance coefficientTensorSymmetric : SymmetricCategory (P).Modules :=
  SheafOfModules.symmetricCategorySheafTensor (P).sheaf

/-- The actual mixed coefficient on the bounded-below flat pullback represents zero. -/
theorem projectiveLineMixedCoefficient_isZero (K : BoundedBelowPerfect.Obj X) :
    IsZero (DerivedCategory.Q.obj
      ((projectiveLineG₁ X).obj
        ((total P).obj ((BoundedBelowPerfect.flatPullback π).obj K))).obj) := by
  let K' := (BoundedBelowPerfect.flatPullback π).obj K
  let A := (total P).obj K'
  let U := (BoundedBelowPerfect.tensorVectorBundleRight L).obj ((inclusion P).obj A)
  let J := (total P).obj U
  let Q := DerivedCategory.Q (C := (P).Modules)
  let R := derivedPushforwardModules π
  let F := (pushforward π).mapHomologicalComplex c
  let σ := ((unit P).app U).hom
  let τ := ((unit P).app K').hom
  let T := (tensorRight L).mapHomologicalComplex c
  have hσ : QuasiIso σ := unit_weak P U
  have hτ : QuasiIso τ := unit_weak P K'
  have hT : QuasiIso (T.map τ) :=
    (perfectTensorRight_waldhausenExact L).weak
      ((BoundedBelowPerfect.inclusion P).map ((unit P).app K')) hτ
  let eσ := @asIso _ _ _ _ (Q.map σ)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (P).Modules σ).2 hσ)
  let eτ := @asIso _ _ _ _ (Q.map (T.map τ))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (P).Modules _).2 hT)
  let eB := (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight L) c).app
    K'.obj
  let e := flasquePushforwardIso π J.obj J.property.1.2 J.property.2 ≪≫
    (R.mapIso eσ).symm ≪≫ (R.mapIso eτ).symm ≪≫ (R.mapIso (Q.mapIso eB)).symm
  change IsZero (DerivedCategory.Q.obj (F.obj J.obj))
  exact (derivedNegativeCoefficient_isZero X K.obj K.property.1).of_iso e

local notation "V" => (BoundedBelowPerfect.waldhausen X)
local notation "W" => (perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X)))
local notation "F₀" => (BoundedBelowPerfect.flatPullback π)
local notation "T₁" => (BoundedBelowPerfect.tensorVectorBundleRight L)

/-- Untwisted direct image of the resolved negative summand is the trivial map on K-groups. -/
theorem projectiveLineG₀_negative_KMap (n : ℕ) :
    KMap ((((BoundedBelowPerfect.flatPullback_exact π).comp
      (BoundedBelowPerfect.tensorVectorBundleRight_exact L)).comp (total_exact P)).comp
        (projectiveLineG₀_exact X)) n = 1 := by
  let F := ((F₀ ⋙ T₁) ⋙ total P) ⋙ projectiveLineG₀ X
  have hz (K : BoundedBelowPerfect.Obj X) : IsZero (DerivedCategory.Q.obj (F.obj K).obj) := by
    let U := (T₁).obj ((F₀).obj K)
    let J := (total P).obj U
    let Q := DerivedCategory.Q (C := (P).Modules)
    let R := derivedPushforwardModules π
    let σ := ((unit P).app U).hom
    have hσ : QuasiIso σ := unit_weak P U
    let eσ := @asIso _ _ _ _ (Q.map σ)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (P).Modules σ).2 hσ)
    let eB := (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight L) c).app ((F₀).obj K).obj
    exact (derivedNegativeCoefficient_isZero X K.obj K.property.1).of_iso
      (flasquePushforwardIso π J.obj J.property.1.2 J.property.2 ≪≫
        (R.mapIso eσ).symm ≪≫ (R.mapIso (Q.mapIso eB)).symm)
  let η : zeroFunctor (C := BoundedBelowPerfect.Obj X) W ⟶ F :=
    { app := fun K => (W).isZero.to_ (F.obj K)
      naturality := fun _ _ _ => (W).isZero.eq_of_src _ _ }
  have hη (K : BoundedBelowPerfect.Obj X) : (W).weq (η.app K) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).1
    exact IsZero.isIso ((DerivedCategory.Q (C := X.Modules)).map_isZero
      ((ObjectProperty.ι (IsPerfectComplex (X := X.toRingedSpace))).map_isZero (W).isZero))
      (hz K) _
  exact (KMap_eq_of_weakNatTrans (zeroFunctor_isExact V W) _ η hη n).symm.trans
    (KMap_zeroFunctor V W n)

/-- Negative-twist direct image of the resolved untwisted summand is the trivial K-map. -/
theorem projectiveLineG₁_untwisted_KMap (n : ℕ) :
    KMap (((BoundedBelowPerfect.flatPullback_exact π).comp (total_exact P)).comp
      (projectiveLineG₁_exact X)) n = 1 := by
  let F := (F₀ ⋙ total P) ⋙ projectiveLineG₁ X
  let η : zeroFunctor (C := BoundedBelowPerfect.Obj X) W ⟶ F :=
    { app := fun K => (W).isZero.to_ (F.obj K)
      naturality := fun _ _ _ => (W).isZero.eq_of_src _ _ }
  have hη (K : BoundedBelowPerfect.Obj X) : (W).weq (η.app K) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).1
    exact IsZero.isIso ((DerivedCategory.Q (C := X.Modules)).map_isZero
      ((ObjectProperty.ι (IsPerfectComplex (X := X.toRingedSpace))).map_isZero (W).isZero))
      (projectiveLineMixedCoefficient_isZero X K) _
  exact (KMap_eq_of_weakNatTrans (zeroFunctor_isExact V W) _ η hη n).symm.trans
    (KMap_zeroFunctor V W n)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
