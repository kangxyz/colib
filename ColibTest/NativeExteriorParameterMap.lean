/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) {T U V : SmoothSite S}

example (ψ : T ⟶ U) (χ : U ⟶ V) : exteriorParameterMap X Y W (ψ ≫ χ) =
    exteriorParameterMap X Y W ψ ≫ exteriorParameterMap X Y W χ :=
  exteriorParameterMap_comp X Y W ψ χ
example (ψ : T ⟶ U) :
    exteriorParameterMap X Y W ψ ≫ exteriorIdentityTarget X Y U W =
    exteriorIdentityTarget X Y T W ≫ (SmoothSite.productMap (𝟙 Y) ψ).left :=
  exteriorParameterMap_target X Y W ψ
