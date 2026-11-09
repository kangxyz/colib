/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterSquares

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) {T U : SmoothSite S} (ψ : T ⟶ U)

example : IsPullback (exteriorParameterMap X Y W ψ) (exteriorIdentitySource X Y T W)
    (exteriorIdentitySource X Y U W) (SmoothSite.productMap (𝟙 X) ψ).left :=
  exteriorParameterMap_source_isPullback X Y W ψ
example : IsPullback (exteriorParameterMap X Y W ψ) (exteriorIdentityTarget X Y T W)
    (exteriorIdentityTarget X Y U W) (SmoothSite.productMap (𝟙 Y) ψ).left :=
  exteriorParameterMap_target_isPullback X Y W ψ
