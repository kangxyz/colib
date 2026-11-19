/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineThom
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenSequence

/-!
# The original localization boundary in a relative line Thom map

The absolute pair sequence maps to the nested pair sequence by the original
quotient projections and the identity of the last quotient. This identifies
the relevant third arrows before composing with the reduced Laurent projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "R" => smoothTransferRepresentable k
local notation "p" => transferPairProjection k
local notation "C" => transferPairCokernelFunctor k

attribute [local irreducible] Cor.graphFunctor transferRepresentable

/-- The transfer-sheaf abelian structure used for the relative line boundary. -/
local instance relativeLineBoundaryAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

private def absoluteToNestedPairSequenceMap
    {U W Y : Sm} (i : U ⟶ W) (v : W ⟶ Y) :
    transferPairSequence k (Arrow.mk v) ⟶ nestedPairTransferSequence k i v :=
  ShortComplex.homMk ((p).app (Arrow.mk i)) ((p).app (Arrow.mk (i ≫ v))) (𝟙 _)
    ((p).naturality (nestedPairFirstArrow k i v)).symm (by
      let β := nestedPairSecondArrow k i v
      change (p).app (Arrow.mk (i ≫ v)) ≫ (C).map β = (p).app (Arrow.mk v) ≫ 𝟙 _
      have h := (p).naturality β
      change (R).map (𝟙 Y) ≫ (p).app (Arrow.mk v) =
        (p).app (Arrow.mk (i ≫ v)) ≫ (C).map β at h
      rw [(R).map_id, Category.id_comp] at h
      exact h.symm.trans (Category.comp_id _).symm)

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 650000 in
-- State the naturality identity on the original reflected transfer triangle.
/-- The absolute open-pair boundary followed by the shifted quotient is the
boundary of the original nested open pairs. -/
theorem effectivePairBoundary_comp_quotient_shift {U W Y : Sm} (i : U ⟶ W) (v : W ⟶ Y)
    [IsOpenImmersion i.left] [IsOpenImmersion v.left] :
    effectivePairBoundary k v ≫ (effectivePairMotiveQuotient k i)⟦(1 : ℤ)⟧' =
      effectiveNestedPairBoundary k i v := by
  let F := effectiveTransferSheaf k
  let a := absoluteToNestedPairSequenceMap k i v
  let t := effectiveTransferSheafTriangleMap k (transferPairSequence_shortExact k v)
    (nestedPairTransferSequence_shortExact k i v) a
  let S := shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)
  let δ := (effectiveOpenPairTransferTriangle k v).mor₃
  let d := effectiveNestedPairBoundary k i v
  let q := F.map ((p).app (Arrow.mk i))
  have ht := t.comm₃
  change δ ≫ S.map q = F.map (𝟙 (transferPairCokernel k v)) ≫ d at ht
  let e := (smoothTransferRepresentableEffectiveIso k).app W
  change (δ ≫ S.map e.hom) ≫ S.map (e.inv ≫ q) = d
  calc
    _ = δ ≫ S.map (e.hom ≫ (e.inv ≫ q)) :=
      (Category.assoc _ _ _).trans (congrArg (δ ≫ ·) (S.map_comp _ _).symm)
    _ = δ ≫ S.map q := congrArg (fun f => δ ≫ S.map f) (e.hom_inv_id_assoc q)
    _ = _ := ht.trans ((congrArg (· ≫ d) (F.map_id _)).trans (Category.id_comp _))

variable {U X W : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  (i : affineLineCylinder.obj U ⟶ W) (l : torusCylinder.obj X ⟶ W)
  (v : W ⟶ affineLineCylinder.obj X)
  (hi : i ≫ v = affineLineCylinder.map j) (hl : l ≫ v = openInclusion.app X)

variable [IsOpenImmersion v.left]
  [IsOpenImmersion i.left] [IsOpenImmersion l.left]
  (hpb : (relativeLineOpenCoverSquare k j i l v hi hl).IsPullback)
  (hcover : Set.range i.left ∪ Set.range l.left = Set.univ)

set_option maxHeartbeats 700000 in
-- Identify the chosen comparison on the actual Laurent chart arrow.
/-- The Laurent chart map and its ambient quotient give the original
open-cover comparison on the relative Laurent quotient. -/
theorem effectivePairMotiveQuotient_relativeLineLaurentComparison :
    effectivePairMotiveQuotient k (torusCylinder.map j) ≫
        (relativeLineLaurentComparison k j i l v hi hl hpb hcover).hom =
      (effectiveSmoothMotive k).map l ≫ effectivePairMotiveQuotient k i := by
  let a := relativeLineLaurentArrow k j i l v hi hl
  let e := relativeLineLaurentComparison k j i l v hi hl hpb hcover
  have he : e.hom = (effectivePairMotiveFunctor k).map a :=
    (relativeLineLaurentComparisonData k j i l v hi hl hpb hcover).property
  have hn := effectivePairMotiveQuotient_naturality_arrow k
    (j := torusCylinder.map j) (j' := i) a
  exact (congrArg (effectivePairMotiveQuotient k (torusCylinder.map j) ≫ ·) he).trans hn

variable [IsOpenImmersion j.left] [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

set_option maxHeartbeats 750000 in
-- Compose the actual quotient and Laurent maps inside the original shift.
/-- On the original relative line the forward Thom map is the absolute
localization boundary followed by the shifted relative Laurent projection. -/
theorem relativeLineThomIso_hom_effectivePairBoundary :
    (relativeLineThomIso k j i l v hi hl hpb hcover).hom =
      effectivePairBoundary k v ≫
        (effectivePairMotiveQuotient k i ≫
          ((relativeLineLaurentComparison k j i l v hi hl hpb hcover).inv ≫
            (effectiveRelativeLaurentRetract k j).r))⟦(1 : ℤ)⟧' := by
  let S := shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)
  let δ := effectivePairBoundary k v
  let q := effectivePairMotiveQuotient k i
  let r := (relativeLineLaurentComparison k j i l v hi hl hpb hcover).inv ≫
    (effectiveRelativeLaurentRetract k j).r
  calc
    _ = effectiveNestedPairBoundary k i v ≫ S.map r :=
      relativeLineThomIso_hom k j i l v hi hl hpb hcover
    _ = (δ ≫ S.map q) ≫ S.map r :=
      congrArg (· ≫ S.map r) (effectivePairBoundary_comp_quotient_shift k i v).symm
    _ = δ ≫ S.map (q ≫ r) :=
      (Category.assoc _ _ _).trans (congrArg (δ ≫ ·) (S.map_comp _ _).symm)

end AlgebraicGeometry.MotivicHomotopy
