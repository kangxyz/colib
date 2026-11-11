/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidencePushPull

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

example : IsFinite (exteriorIncidenceProductOuter X Z T Y z w) :=
  exteriorIncidenceProductOuter_isFinite X Z T Y z w hz hw

example : IsClosedImmersion (exteriorOuterDiagonal X Z T) := inferInstance

example (p : exteriorIncidenceProduct X Y Z T z w) :
    (correspondenceIncidenceMap (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)).residueDegree
        ((nativeExteriorIncidenceIso X Y Z T z w hz hw).hom p) =
      (exteriorIncidenceProductOuter X Z T Y z w).residueDegree p :=
  nativeExteriorIncidenceMap_residueDegree X Y Z T z w hz hw p

example (c d : AlgebraicCycle (exteriorOuterProduct X Z T) ℤ)
    (h : finiteCyclePushforward (exteriorOuterDiagonal X Z T) c =
      finiteCyclePushforward (exteriorOuterDiagonal X Z T) d) : c = d :=
  finiteCyclePushforward_injective_of_isClosedImmersion (exteriorOuterDiagonal X Z T) h

#check exteriorIncidenceProductOuter_isPullback
#check exteriorIncidence_fixedLabel_pushPull
#check nativeExteriorIncidence_pushforward_flatPullback

/-! Direct consumers of the two native push-pull comparisons. -/

attribute [local instance] Classical.propDecidable

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "I" => correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "BT" => exteriorOuterProduct X Z T
local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "qT" => exteriorIncidenceProductOuter X Z T Y z w
local notation3 (prettyPrint := false) "πI" =>
  (pullback.fst (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom)
local notation3 (prettyPrint := false) "πB" =>
  (pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom)
local notation3 (prettyPrint := false) "sI" =>
  (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom)
local notation3 (prettyPrint := false) "sB" => (pullback.fst X.hom Z.hom ≫ X.hom)
local notation3 (prettyPrint := false) "sIT" => (πI ≫ sI)
local notation3 (prettyPrint := false) "sBT" => (πB ≫ sB)

local instance : LocallyOfFiniteType sI := by
  dsimp only [correspondenceIncidenceLeft]
  infer_instance

example (x : I) (p : BT) (hp : πB p = q x) :
    let d := relativeDimension (C).dimensionFunction sI x
    let r := exteriorParameterDimension T
    ((q).residueDegree x : ℤ) * flatPullbackWeight C sBT πB (d + (r : ℤ)) p =
      ∑ᶠ a ∈ (qT).base ⁻¹' {p},
        if πI a = x then
          flatPullbackWeight C sIT πI (d + (r : ℤ)) a * ((qT).residueDegree a : ℤ)
        else 0 :=
  exteriorIncidence_fixedLabel_pushPull X Y Z T z w hz hw x p hp

example
    (n : ℤ) (α : CycleGroup C sI n) :
    letI := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom z w hz hw
    letI := isFinite_correspondenceIncidenceMap (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
      (nativeExteriorPoint_admissible X Y T z hz)
      (nativeExteriorPoint_admissible Y Z T w hw)
    let r := exteriorParameterDimension T
    finiteCyclePushforward
        (correspondenceIncidenceMap (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
          (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw))
        (finiteCyclePushforward (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom
          (flatPullback C sIT sI πI rfl r
            (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w) n α).val) =
      finiteCyclePushforward (exteriorOuterDiagonal X Z T)
        (flatPullback C sBT sB πB rfl r
          (relativeDimension_exteriorOuterProjection X Z T) n
          (properPushforward C sI sB q
            (by simp only [← Category.assoc, correspondenceIncidenceMap_fst]) n α)).val :=
  nativeExteriorIncidence_pushforward_flatPullback X Y Z T z w hz hw n α
