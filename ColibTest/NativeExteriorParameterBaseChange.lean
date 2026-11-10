/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterBaseChange

/-!
# In-package checks for native exterior ParameterBaseChange
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) {T U : SmoothSite S} (ψ : T ⟶ U)

example [Flat ψ.left] : Flat (exteriorParameterMap X Y W ψ) := inferInstance
example [IsFinite ψ.left] : IsFinite (exteriorParameterMap X Y W ψ) := inferInstance
example [IsClosedImmersion ψ.left] : IsClosedImmersion (exteriorParameterMap X Y W ψ) :=
  inferInstance

example : IsPullback (exteriorParameterMap X Y W ψ)
    (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)
    (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom) ψ.left :=
  exteriorParameterMap_isPullback X Y W ψ
