/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameter
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SmoothMotive
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeParameter
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Native
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Relative effective motives and the original smooth product -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

local instance smoothProductCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance smoothProductSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "E" => EffectiveMotivesMinus k
local notation "M" => effectiveSmoothMotive k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The canonical abelian structure on the sheaves with transfers. -/
local instance smoothProductAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The signed convolution tensor used to compare product pairs. -/
local instance smoothProductMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- Tensoring the motive of a pair with a smooth motive gives the relative motive
of the original product pair. -/
def effectivePairProductRightIso {U V : Sm} (j : U ⟶ V) [IsOpenImmersion j.left] (Y : Sm) :
    effectivePairMotive k j ⊗ (M).obj Y ≅ effectivePairMotive k ((parameterProduct Y).map j) :=
  (effectiveRepresentedRightParameterIso θ Y).app (effectivePairMotive k j) ≪≫
    effectiveSmoothParameterPairIso (θ Y) j

set_option maxHeartbeats 800000 in
-- Project the comparison at its literal effective endpoints.
/-- The product comparison uses the original parameter and quotient maps. -/
theorem effectivePairProductRightIso_hom {U V : Sm} (j : U ⟶ V)
    [IsOpenImmersion j.left] (Y : Sm) :
    (effectivePairProductRightIso k j Y).hom =
      (effectiveRepresentedRightParameterIso θ Y).hom.app (effectivePairMotive k j) ≫
        (effectiveSmoothParameterPairIso (θ Y) j).hom :=
  (rfl)

end AlgebraicGeometry.MotivicHomotopy
