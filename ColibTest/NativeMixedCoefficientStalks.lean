/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientStalks

/-!
# Direct consumers at the actual native mixed incidence stalk

The original support scalar map and the original middle-pair stalk map are the
ones used by the native original-Tor/support-Koszul comparison. The consumer
checks that their composition is the literal mixed-chart scalar path.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

universe u

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz

variable (x : nativeMixedGraphIncidence X Y T U ψ z hz t)

example :
    (((nativeMixedCoefficientChart X Y T U ψ z hz t).stalkMap
      (correspondenceIncidenceToSupportProduct f g h a b x)).hom).comp
        (nativeMixedCoefficientMiddleStalkMap X Y T U ψ z hz t x).hom =
    (correspondenceIncidenceSupportStalkMap f g h a b x).comp
      ((correspondenceMiddlePair f g h).stalkMap
        (correspondenceIncidenceAmbientInclusion f g h a b x)).hom :=
  nativeMixedCoefficientMiddleStalkMap_comp X Y T U ψ z hz t x

example (d : nativeMixedGraphSupportProduct X Y T U ψ z hz t) :
    (nativeMixedCoefficientChartStalkIso X Y T U ψ z hz t d).hom =
      (nativeMixedCoefficientChart X Y T U ψ z hz t).stalkMap d :=
  nativeMixedCoefficientChartStalkIso_hom X Y T U ψ z hz t d
