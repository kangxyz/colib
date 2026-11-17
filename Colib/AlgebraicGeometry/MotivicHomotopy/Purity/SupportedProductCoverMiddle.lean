/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverTriangles

/-! # The middle vertex of the product-pair cover comparison -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme SmoothSite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] supportedProductCorSheafify supportedProductSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "M" => effectiveSmoothMotive k

attribute [local instance] supportedProductAbelian supportedProductMonoidal
  supportedProductTensorAdditive tensorLeft_preservesBinaryBiproducts

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

-- Both presentations use the same relative product and product map on each chart.
attribute [local irreducible] SmoothSite.product SmoothSite.productMap effectivePairProductRightIso

set_option maxHeartbeats 950000 in
-- Identify the chart biproducts with the two actual middle triangle objects.
/-- The middle cover isomorphism is the tensor biproduct comparison followed by
the two actual product-pair isomorphisms. -/
@[expose] def effectivePairProductOpenCoverMiddleIso (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact)
    (h' : (productCoverRow k j sq).ShortExact) :
    (tensorLeft (effectivePairMotive k j)).obj
        (effectiveMayerVietorisTriangleOfPushout k sq h).obj₂ ≅
      (effectivePairOpenCoverTriangle k (j := smoothPairProductCoverMap j sq) h').obj₂ := by
  let H := tensorLeft (effectivePairMotive k j)
  let B := effectiveTransferSheaf k
  let Q := productCoverQuotientSquare k j sq
  let Y₂ := (M).obj sq.X₂
  let Y₃ := (M).obj sq.X₃
  let v₂ : H.obj Y₂ ≅ B.obj Q.X₂ := effectivePairProductRightIso k j sq.X₂
  let v₃ : H.obj Y₃ ≅ B.obj Q.X₃ := effectivePairProductRightIso k j sq.X₃
  let e : H.obj (Y₂ ⊞ Y₃) ≅ (B.obj Q.X₂ ⊞ B.obj Q.X₃) :=
    H.mapBiprod Y₂ Y₃ ≪≫ biprod.mapIso v₂ v₃
  exact e

end AlgebraicGeometry.MotivicHomotopy
