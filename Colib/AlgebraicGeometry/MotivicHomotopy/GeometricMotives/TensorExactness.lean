/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Monoidal
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.AssociatorShift
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Exactness of the stabilized tensor from its Lefschetz shift comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction
open scoped MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local instance geometricTensorExactCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance geometricTensorExactSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

/-- The canonical abelian structure used in the tensor exactness proof. -/
local instance geometricTensorExactGenericAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (LargePresheaves k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "E" => EffectiveMotivesMinus k
local notation "P" => isEffectiveGeometric k
local notation "D" => GeometricMotives k

local notation "EffGm" => EffectiveGeometricMotives k
set_option quotPrecheck false in
local notation "d₀" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The signed convolution tensor on effective motives. -/
local instance geometricTensorExactEffectiveMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory d₀

/-- The symmetry of signed convolution on effective motives. -/
local instance geometricTensorExactEffectiveSymmetric : SymmetricCategory E :=
  effectiveSignedConvolutionSymmetricCategory d₀

local instance geometricTensorExactEffectiveProperty : (P).IsMonoidal :=
  effectiveGeometricIsMonoidal k d₀

set_option quotPrecheck false in
local notation "L" => geometricEffectiveLefschetzMotive k
set_option quotPrecheck false in
local notation "αL" => geometricTensorRightLefschetzIso k (effectiveLefschetzTensorComparison k)
set_option quotPrecheck false in
local notation "βL" => geometricEffectiveLefschetz_braiding k d₀

local instance geometricTensorExactEffectiveMonoidalPreadditive : MonoidalPreadditive E :=
  effectiveSignedConvolutionMonoidalPreadditive d₀

/-- The two shifts of signed convolution and their integer sign compatibility. -/
local instance geometricTensorExactEffectiveCommShift₂Int : (curriedTensor E).CommShift₂Int :=
  effectiveSignedConvolutionCommShift₂Int d₀

/-- The shift isomorphism for left tensoring in effective geometric motives. -/
local instance stableGeometricTensorLeftShift (A : EffGm) : (tensorLeft A).CommShift ℤ :=
  geometricTensorLeftCommShift k A

/-- The shift isomorphism for right tensoring in effective geometric motives. -/
local instance stableGeometricTensorRightShift (A : EffGm) : (tensorRight A).CommShift ℤ :=
  geometricTensorRightCommShift k A

set_option maxHeartbeats 650000 in
-- Apply shift detection to the actual postcomposition with the faithful inclusion.
private theorem actualStableLefschetzComparisonShift
    (h : NatTrans.CommShift (effectiveLefschetzTensorComparison k).hom ℤ) :
    NatTrans.CommShift (αL).hom ℤ := by
  let J := effectiveGeometricMotivesInclusion k
  let e := effectiveLefschetzTensorComparison k
  let a := geometricTensorRightLefschetzIso k e
  have he := geometricTensorRightLefschetzIsoPostcomp_commShift k e h
  have ha : NatTrans.CommShift (Functor.whiskerRight a.hom J) ℤ :=
    geometricTensorRightLefschetzIso_postcomp_commShift k e he
  exact NatTrans.CommShift.of_comp_faithful (G := J) ha

set_option maxHeartbeats 650000 in
-- Restrict the middle associator comparison along the fully faithful inclusion.
private theorem geometricEffectiveMiddleAssociatorCommShift :
    MiddleAssociatorCommShift EffGm := by
  let J := effectiveGeometricMotivesInclusion k
  let := geometricInclusionMonoidalCommShift k
  exact middleAssociatorCommShift_of_faithful J
    (effectiveSignedConvolution_middleAssociatorCommShift d₀)

private theorem geometricEffectiveTensorLeft_isTriangulated
    (h : ∀ A : E, (tensorLeft A).IsTriangulated) (A : EffGm) :
    (tensorLeft A).IsTriangulated := by
  let : (tensorLeft A.obj).IsTriangulated := h A.obj
  exact geometricTensorLeft_isTriangulated k A

private theorem geometricEffectiveLefschetzTensor_isTriangulated
    (h : NatTrans.CommShift (αL).hom ℤ) : (tensorRight (L)).IsTriangulated := by
  let e := (αL)
  let : NatTrans.CommShift e.hom ℤ := h
  let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  exact Functor.isTriangulated_of_iso e.symm

set_option maxHeartbeats 650000 in
-- Check the exact finite-stage transport with the original geometric shift choices.
/-- Exactness in both arguments uses the original Lefschetz tensor comparison,
with the signed effective shifts. -/
theorem geometricMotivesTensorExact_of_lefschetzShift
    (h₀ : NatTrans.CommShift (effectiveLefschetzTensorComparison k).hom ℤ) :
    (∀ A : D, ∃ c : (tensorLeft A).CommShift ℤ, letI := c; (tensorLeft A).IsTriangulated) ∧
      (∀ A : D, ∃ c : (tensorRight A).CommShift ℤ, letI := c; (tensorRight A).IsTriangulated) := by
  let h := actualStableLefschetzComparisonShift k h₀
  let : NatTrans.CommShift (αL).hom ℤ := h
  let q := (Functor.FullyFaithful.ofFullyFaithful (geometricLefschetzTensor k)).ofIso (αL).symm
  let : (tensorRight (L)).Full := q.full
  let : (tensorRight (L)).Faithful := q.faithful
  let (B : EffGm) : (tensorLeft B).IsTriangulated :=
    geometricEffectiveTensorLeft_isTriangulated k (effectiveSignedTensorLeft_isTriangulated d₀) B
  let : (tensorRight (L)).IsTriangulated :=
    geometricEffectiveLefschetzTensor_isTriangulated k h
  let (B : EffGm) : NatTrans.CommShift (Stabilization.tensorLeftTwistIso (L) B).hom ℤ :=
    geometricEffectiveMiddleAssociatorCommShift k B L
  exact ⟨geometricMotivesTensorLeftExactOfTate k (αL) (βL),
    geometricMotivesTensorRightExactOfTate k (αL) (βL)⟩

end AlgebraicGeometry.MotivicHomotopy
