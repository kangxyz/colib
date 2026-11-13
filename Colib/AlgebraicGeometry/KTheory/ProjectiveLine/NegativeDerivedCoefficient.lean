/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectVectorBundleTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DerivedPushforwardTwist
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise

/-! # Vanishing of the derived negative coefficient on the projective line -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula Stacks.DerivedTensor.RingedSite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  CategoryTheory.sheafCompose Stacks.SheafOfModules.Tensor.ringSheaf

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

local instance : SheafOfModules.IsFiniteLocallyFree (R := (P).ringCatSheaf) L :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local instance tensorMonoidal : MonoidalCategory (P).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (P).sheaf

local instance tensorAdditive : MonoidalPreadditive (P).Modules := by
  let := Abelian.hasFiniteBiproducts (C := (P).Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor (P).sheaf

local instance complexMonoidal : MonoidalCategory (CochainComplex (P).Modules ℤ) :=
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory (P).sheaf

/-- The derived coefficient of `𝒪(-1) ⊗ π* K` vanishes, by the actual projection formula. -/
theorem derivedNegativeCoefficient_isZero (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    IsZero ((derivedPushforward (π).toLRSHom.toShHom).obj
      (DerivedCategory.Q.obj (((tensorLeft L).mapHomologicalComplex c).obj
        (((pullback π).mapHomologicalComplex c).obj K)))) := by
  let φ := (π).toLRSHom.toShHom
  let Q := DerivedCategory.Q (C := (P).Modules)
  let R := derivedPushforward φ
  let A := derivedPullback φ
  let T := canonicalDerivedTensorProduct (P).sheaf
  let L₀ := (DerivedCategory.singleFunctor (P).Modules 0).obj L
  let K₀ := DerivedCategory.Q.obj K
  let K' := ((pullback π).mapHomologicalComplex c).obj K
  let eK : A.obj K₀ ≅ Q.obj K' :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat φ
      (fun x => Flat.stalkMap π x) K
  let eL := (DerivedCategory.singleFunctorIsoCompQ (P).Modules 0).app L
  let e : ((T.tensor.obj L₀).obj (A.obj K₀)) ≅
      Q.obj (((tensorLeft L).mapHomologicalComplex c).obj K') :=
    (T.tensor.mapIso eL).app _ ≪≫ (T.tensor.obj _).mapIso eK ≪≫
      T.comparisonLeft _ _ (kFlat_single_of_isFiniteLocallyFree P L inferInstance) ≪≫
      Q.mapIso (TotalTensorComplex.SingleTensor.singleTensorIso L K')
  have hz : IsZero (R.obj L₀) := by
    change IsZero ((Stacks.Duality.derivedPushforward π).obj L₀)
    exact Stacks.Duality.ProjectiveSpace.isZero_derivedPushforward_twistOver 0 X
      (d := -1) (by norm_num) (by norm_num)
  let TY := canonicalDerivedTensorProduct X.sheaf
  let G := TY.tensor.flip.obj K₀
  let := TY.commShift_left K₀
  have := TY.exact_left K₀
  let : G.Additive := by
    change (TY.tensor.flip.obj K₀).Additive
    infer_instance
  have hz' : IsZero (((derivedTensorProductFunctor X.sheaf).obj (R.obj L₀)).obj K₀) :=
    G.map_isZero hz
  let hp := Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isPerfect
    φ L₀ K₀ hK.isPerfect
  exact hz'.of_iso ((R.mapIso e).symm ≪≫
    (@asIso _ _ _ _ (projectionFormulaMap φ L₀ K₀) hp).symm)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
