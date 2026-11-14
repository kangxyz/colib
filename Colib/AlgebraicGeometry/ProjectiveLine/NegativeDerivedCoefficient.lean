/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.Util.References

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DerivedPushforwardTwist
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

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

namespace AlgebraicGeometry.projectiveSpaceOver

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
        (((Scheme.Modules.pullback π).mapHomologicalComplex c).obj K)))) := by
  let φ := (π).toLRSHom.toShHom
  let Q := DerivedCategory.Q (C := (P).Modules)
  let R := derivedPushforward φ
  let A := derivedPullback φ
  let T := canonicalDerivedTensorProduct (P).sheaf
  let L₀ := (DerivedCategory.singleFunctor (P).Modules 0).obj L
  let K₀ := DerivedCategory.Q.obj K
  let K' := ((Scheme.Modules.pullback π).mapHomologicalComplex c).obj K
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

/-- Pullback along the projective-line projection followed by left tensoring by the native
twisting sheaf `𝒪(-1)`. -/
abbrev negativePullback :
    X.Modules ⥤ (P).Modules :=
  Scheme.Modules.pullback π ⋙ tensorLeft L

instance : (negativePullback X).Additive := by
  dsimp [negativePullback]
  infer_instance

local instance : PreservesFiniteLimits (negativePullback X) := by
  let := AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat π
  let : PreservesFiniteLimits (tensorLeft L) := by
    change PreservesFiniteLimits ((curriedTensor (P).Modules).obj L)
    have e : (curriedTensor (P).Modules).obj L =
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (P).sheaf).obj L :=
      congrArg (fun T => T.obj L) (SheafOfModules.curriedTensor_sheafTensor (P).sheaf)
    rw [e]
    exact Stacks.SheafOfModules.FlatTensorShortExact.preservesFiniteLimits_sheafTensor_obj_of_isFlat
      _ L (@Scheme.Modules.isFlat_of_isFiniteLocallyFree P L inferInstance)
  dsimp [negativePullback]
  infer_instance

local instance : PreservesFiniteColimits (negativePullback X) := by
  let : PreservesFiniteColimits (tensorLeft L) := by
    change PreservesFiniteColimits ((curriedTensor (P).Modules).obj L)
    have e : (curriedTensor (P).Modules).obj L =
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (P).sheaf).obj L :=
      congrArg (fun T => T.obj L) (SheafOfModules.curriedTensor_sheafTensor (P).sheaf)
    rw [e]
    exact Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj _ L
  dsimp [negativePullback]
  infer_instance

/-- The bounded-below derived direct image of the actual left twist of a pulled-back perfect
coefficient vanishes. No choice of strict representative is required. -/
@[colib_tag "COL-1290",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativePerfectGeneration.lean:155"
    "generalization" "Vanishing of the actual left twist of a pulled-back perfect coefficient."]
theorem isZero_projectiveLineNegativePullbackPlus (K : DerivedCategory.Plus X.Modules)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K.obj) :
    IsZero ((Scheme.Modules.pushforward π).rightDerivedFunctorPlus.obj
      ((negativePullback X).rightDerivedFunctorPlus.obj K)) := by
  let F := negativePullback X
  let φ := (π).toLRSHom.toShHom
  let G := modulePushforward φ
  let R := derivedPushforward φ
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨C, hCa, ⟨e⟩⟩ := K.obj.exists_iso_Q_obj_of_isGE a
  let C' : CochainComplex.Plus X.Modules := ⟨C, ⟨a, hCa⟩⟩
  let eQ := (DerivedCategory.Plus.QCompιIso X.Modules).app C'
  let eK : DerivedCategory.Plus.Q.obj C' ≅ K :=
    DerivedCategory.Plus.ι.preimageIso (eQ ≪≫ e.symm)
  have hp : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) C :=
    RingedSpace.isPerfectComplex_of_isPerfect_representation hK ⟨e.symm⟩
  let H := F.rightDerivedFunctorPlus.obj K
  obtain ⟨b, hb⟩ := H.property
  obtain ⟨j⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    G R (derivedPushforwardUnit φ)
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective φ I hI) H b hb
  have hF := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let C'' := F.mapCochainComplexPlus.obj C'
  let D := HomotopyCategory.Plus.quotient X.Modules
  let D' := HomotopyCategory.Plus.quotient (P).Modules
  let Qh := DerivedCategory.Plus.Qh (C := (P).Modules)
  let η := (asIso F.rightDerivedFunctorPlusUnith).app (D.obj C')
  let e₀ : DerivedCategory.Plus.Q.obj C'' ≅ Qh.obj (D'.obj C'') :=
    (DerivedCategory.Plus.quotientCompQhIso (P).Modules).symm.app C''
  let e₁ : Qh.obj (D'.obj C'') ≅ Qh.obj (F.mapHomotopyCategoryPlus.obj (D.obj C')) :=
    Qh.mapIso (F.quotientCompMapHomotopyCategoryPlusIso.symm.app C')
  let e₂ := F.rightDerivedFunctorPlus.mapIso
    ((DerivedCategory.Plus.quotientCompQhIso X.Modules).app C' ≪≫ eK)
  let eH : DerivedCategory.Q.obj C''.obj ≅ H.obj :=
    ((DerivedCategory.Plus.QCompιIso (P).Modules).app C'').symm ≪≫
      DerivedCategory.Plus.ι.mapIso (e₀ ≪≫ e₁ ≪≫ η ≪≫ e₂)
  have hzero := derivedNegativeCoefficient_isZero X C hp
  have hzero' : IsZero (R.obj H.obj) :=
    hzero.of_iso (R.mapIso eH.symm)
  exact IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _ (hzero'.of_iso j.symm)

end AlgebraicGeometry.projectiveSpaceOver
