/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidence

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

example : nativeMixedGraphToSupport X Y T U ψ z hz t ≫
    exteriorIdentitySource X Y T (integralComponentAt z) =
    nativeMixedGraphSource X Y T U ψ z hz t :=
  nativeMixedGraphToSupport_source X Y T U ψ z hz t

example : nativeMixedGraphToSupport X Y T U ψ z hz t ≫
    exteriorParameterMap X Y (integralComponentAt z) ψ =
    nativeMixedGraphToChangedSupport X Y T U ψ z hz t :=
  nativeMixedGraphToSupport_parameter X Y T U ψ z hz t
