/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceHigherTor

/-! # Direct positive-degree actual Tor consumer, without parameter flatness -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

universe u

example {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
    (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
    (t : genericPoints (SmoothSite.product X T).left)
    (x : nativeMixedGraphIncidence X Y T U ψ z hz t) (n : ℕ) :
    IsZero (correspondenceIncidenceAmbientTor (SmoothSite.product X T).hom
      (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
      (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) x (n + 1)) :=
  isZero_nativeMixedIncidenceAmbientTor_succ X Y T U ψ z hz t x n
