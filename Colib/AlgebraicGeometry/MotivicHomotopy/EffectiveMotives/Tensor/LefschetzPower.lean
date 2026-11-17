/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeLefschetz
public import Colib.CategoryTheory.Triangulated.Stabilization.Stages
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Powers of the effective Lefschetz tensor -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

/-- The canonical additive sheafification on the Nisnevich correspondence site. -/
local instance lefschetzPowerCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The canonical additive sheafification on the smooth Nisnevich site. -/
local instance lefschetzPowerSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "E" => EffectiveMotivesMinus k
local notation "B" => SmoothSite.base S
local notation "M" => effectiveSmoothMotive k
local notation "L" => effectiveLefschetzTwistFunctor k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The canonical abelian structure on sheaves with transfers. -/
local instance lefschetzPowerAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The effective tensor carries the signed convolution of transfer complexes. -/
local instance lefschetzPowerMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- The symmetry moves the Lefschetz factor past the tensor input. -/
local instance lefschetzPowerSymmetric : SymmetricCategory E :=
  effectiveSignedConvolutionSymmetricCategory θ

/-- The Lefschetz power of the base motive acts by the corresponding original
iterate of the effective Lefschetz twist. -/
def effectiveLefschetzPowerTensorIso (A : E) (c : ℕ) :
    (Stabilization.iterate L c).obj ((M).obj B) ⊗ A ≅ (Stabilization.iterate L c).obj A := by
  let K := effectiveLefschetzMotive k
  let e := effectiveLefschetzTensorIso k
  induction c with
  | zero =>
    exact (tensorRight A).mapIso (effectiveSignedConvolutionUnitIso θ).symm ≪≫ λ_ A
  | succ c h =>
    let C := (Stabilization.iterate L c).obj ((M).obj B)
    exact (tensorRight A).mapIso (e.app C).symm ≪≫
      α_ C K A ≪≫ (tensorLeft C).mapIso (β_ K A) ≪≫ (α_ C A K).symm ≪≫
      e.app (C ⊗ A) ≪≫ (L).mapIso h

end AlgebraicGeometry.MotivicHomotopy
