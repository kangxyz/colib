/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothProductComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OrientationDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedGraphDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomGraphGeometry
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The supported Thom graph on open restrictions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

local instance thomGraphBasicCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance thomGraphBasicSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "E" => EffectiveMotivesMinus k
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k

local instance thomGraphBasicBaseNoetherian :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The canonical abelian structure on sheaves with transfers. -/
local instance thomGraphBasicAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The effective signed tensor used in the supported Thom graph. -/
local instance thomGraphBasicMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- The original graph followed by the inverse product comparison and the tensor of a class. -/
def effectivePairThomGraph {A V Y : Sm} {j : A ⟶ V} [IsOpenImmersion j.left]
    (p : V ⟶ Y) {K : E} (t : effectivePairMotive k j ⟶ K) :
    effectivePairMotive k j ⟶ K ⊗ (M).obj Y :=
  (Φ).map (pairProductGraph j p) ≫ (effectivePairProductRightIso k j Y).inv ≫
    (t ▷ (M).obj Y)

set_option maxHeartbeats 1000000 in
-- Use the pair graph with the original inverse-image domain and product target.
/-- The graph over an open chart lands in the product with the fixed original support. -/
def effectiveRestrictedThomGraph {A V Z : Sm} (p : V ⟶ Z) (j : A ⟶ V)
    [IsOpenImmersion j.left] (W : Z.left.Opens) {K : E}
    (classMap : effectivePairMotive k j ⟶ K) :
    (relativeOpenRestrictionMotive k p j).obj W ⟶ K ⊗ (M).obj ((opensFunctor Z).obj W) :=
  let Y := (opensFunctor Z).obj W
  (Φ).map (openRestrictionProductGraphArrowMap p j W) ≫
    (effectivePairProductRightIso k j Y).inv ≫ (tensorRight ((M).obj Y)).map classMap

/-- The top open of the smooth scheme is the original smooth scheme. -/
def smoothTopOpenIso (Z : Sm) : (opensFunctor Z).obj ⊤ ≅ Z := by
  let j := SmoothSite.openInclusion Z ⊤
  let I := forgetScheme S
  letI : IsIso (I.map j) := inferInstanceAs (IsIso Z.left.topIso.hom)
  letI : IsIso j := isIso_of_reflects_iso j I
  exact asIso j

end AlgebraicGeometry.MotivicHomotopy
