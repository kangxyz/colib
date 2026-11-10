/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceTorCoefficient

/-! # Direct native consumer for the actual signed Tor coefficient -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme
open Function.locallyFinsuppWithin

universe u

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

example
    (x : genericPoints (nativeMixedGraphIncidence X Y T U ψ z hz t)) :
    correspondenceIncidenceTorCoefficient k f g h a b x = 1 :=
  nativeMixedMatchingIncidenceTorCoefficient_eq_one X Y T U ψ z hz x

open Classical in
example :
    letI := isIntegral_nativeMixedMatchingIncidence X Y T U ψ z hz
    incidenceTorCycle f g h a b (nativeExteriorPoint_admissible X Y U z hz) =
      single (genericPoint (nativeMixedGraphIncidence X Y T U ψ z hz t)) 1 :=
  nativeMixedMatchingIncidenceTorCycle_eq_single X Y T U ψ z hz
