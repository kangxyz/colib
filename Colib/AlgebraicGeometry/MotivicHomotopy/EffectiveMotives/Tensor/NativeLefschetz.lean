/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.LefschetzComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.NativeParameter
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The actual effective Lefschetz tensor -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

local instance nativeLefschetzCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance nativeLefschetzSmoothSheafify :
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

/-- The original abelian structure on the Nisnevich transfer sheaves. -/
local instance nativeLefschetzAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The effective tensor obtained by localizing signed convolution of transfer complexes. -/
local instance nativeLefschetzMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- The original reduced-torus projector is the complement of the unit-section projector. -/
theorem torusReducedRetract_projector :
    (torusReducedRetract k).r ≫ (torusReducedRetract k).i =
      𝟙 _ - (effectiveMotive k).map
        ((Cor.graphFunctor k).map (toBase Gm ≫ SmoothSite.torusOne S)) := by
  let F := Cor.graphFunctor k
  let M := effectiveMotive k
  let a := toBase Gm
  let b := SmoothSite.torusOne S
  have h : M.map (F.map (a ≫ b)) = M.map (F.map a) ≫ M.map (F.map b) :=
    (M.congr_map (F.map_comp a b)).trans (M.map_comp (F.map a) (F.map b))
  exact (torusReducedProjection_inclusion k).trans (congrArg (𝟙 _ - ·) h.symm)

/-- The original Lefschetz transition is the tensor with the shifted reduced torus. -/
def effectiveLefschetzTensorIso :
    tensorRight (effectiveLefschetzMotive k) ≅ effectiveLefschetzTwistFunctor k :=
  effectiveRightLefschetzIso θ
    (Cor.tensorRightIsoParameterProduct Gm) (Cor.tensorRightIsoParameterProduct B)
    (Cor.tensorRightIsoParameterProduct_naturality (SmoothSite.torusOne S))
    (Cor.tensorRightIsoParameterProduct_naturality (toBase Gm))
    (torusReducedRetract k) (torusReducedRetract_projector k)

end AlgebraicGeometry.MotivicHomotopy
