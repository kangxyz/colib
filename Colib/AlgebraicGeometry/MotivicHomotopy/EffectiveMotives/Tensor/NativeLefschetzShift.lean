/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.LefschetzComparisonShift
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeLefschetz
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeParameterShift
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The signed shift of the effective Lefschetz tensor -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

local instance nativeLefschetzShiftCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance nativeLefschetzShiftSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "E" => EffectiveMotivesMinus k
local notation "Gm" => SmoothSite.multiplicativeGroupObject S
local notation "B" => SmoothSite.base S
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The abelian structure of the transfer sheaves used in the Lefschetz shift comparison. -/
local instance nativeLefschetzShiftAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The effective monoidal structure whose tensor is used in the Lefschetz shift comparison. -/
local instance nativeLefschetzShiftMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- The signed Lefschetz comparison inherits shift compatibility from the original
projective reduced torus adjunction comparison. -/
theorem effectiveLefschetzTensorIso_commShift_of_projective
    (h : NatTrans.CommShift (projectiveEffectiveTorusNatIso k).hom ℤ) :
    letI := effectiveSignedConvolutionCommShift₂Int θ
    NatTrans.CommShift (effectiveLefschetzTensorIso k).hom ℤ := by
  let d := Cor.tensorRightIsoParameterProduct Gm
  let b := Cor.tensorRightIsoParameterProduct B
  let hu := Cor.tensorRightIsoParameterProduct_naturality (SmoothSite.torusOne S)
  let hp := Cor.tensorRightIsoParameterProduct_naturality (toBase Gm)
  let r := torusReducedRetract k
  let hr := torusReducedRetract_projector k
  exact effectiveRightLefschetzIso_commShift_of_reduced θ d b hu hp r hr
    (effectiveRightReducedTorusIso_commShift θ d b hu hp r hr
      (effectiveNativeParameterCompIso_commShift θ Gm d) h)

end AlgebraicGeometry.MotivicHomotopy
