/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphInterchange

/-! # Direct native consumer for graph interchange on signed native cycles -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "gT" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "ΓX" =>
  graphCorrespondenceOfComponents f g (SmoothSite.productMap (𝟙 X) ψ).left
    (MorphismProperty.Over.w _) (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product X T)))
local notation3 (prettyPrint := false) "ΓY" =>
  graphCorrespondenceOfComponents gT h (SmoothSite.productMap (𝟙 Y) ψ).left
    (MorphismProperty.Over.w _) (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product Y T)))

example :
    incidenceTorPairing f g h ΓX (nativeExteriorPrime X Y U z hz) =
      incidenceTorPairing f gT h (nativeExteriorPrime X Y T z hz) ΓY :=
  nativeExteriorPrime_graph_interchange X Y T U ψ z hz

example (α : finiteCorrespondences X.hom Y.hom) :
    incidenceTorPairing f g h ΓX (nativeExterior X Y U α) =
      incidenceTorPairing f gT h (nativeExterior X Y T α) ΓY :=
  nativeExterior_graph_interchange X Y T U ψ α

-- The original negative multiplicity is retained, not replaced by a natural coefficient.
example (n : ℤ) :
    incidenceTorPairing f g h ΓX
      (nativeExterior X Y U (singleFiniteCorrespondence X.hom Y.hom z hz (-n))) =
      incidenceTorPairing f gT h
        (nativeExterior X Y T (singleFiniteCorrespondence X.hom Y.hom z hz (-n))) ΓY :=
  nativeExterior_graph_interchange X Y T U ψ
    (singleFiniteCorrespondence X.hom Y.hom z hz (-n))
