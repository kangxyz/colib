/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedGraphPushforward

/-! # Direct native consumer for the actual degree-weighted finite map -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme
open Function.locallyFinsuppWithin

universe u

attribute [local instance] isIntegral_integralComponentAt

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "t" => nativeMixedMatchingComponent X Y T z hz
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz

open Classical in
example :
    (incidenceTorCorrespondence f g h a b
      (isFiniteCorrespondencePoint_graphMap f g (SmoothSite.productMap (𝟙 X) ψ).left
        (MorphismProperty.Over.w _) t)
      (nativeExteriorPoint_admissible X Y U z hz)).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f (SmoothSite.product Y T).hom h
        (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint_admissible X Y T z hz)
      finiteCyclePushforward
        (correspondenceGraphPostcompositionMap f (SmoothSite.product Y T).hom h
          (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
          (nativeExteriorPoint X Y T z hz))
        (single (genericPoint (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme)
          1) :=
  nativeMixedMatchingIncidenceTor_val X Y T U ψ z hz
