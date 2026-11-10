/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceIso

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (hRange : Set.range (exteriorIdentitySource X Y T (integralComponentAt z)) ⊆
    Set.range (nativeParameterGraphSource X T U ψ t))

noncomputable example : exteriorIdentitySupport X Y T (integralComponentAt z) ≅
    nativeMixedGraphIncidence X Y T U ψ z hz t :=
  nativeMixedGraphIncidenceIso X Y T U ψ z hz t hRange

example : (nativeMixedGraphIncidenceIso X Y T U ψ z hz t hRange).hom ≫
    (nativeMixedGraphIncidenceIso X Y T U ψ z hz t hRange).inv = 𝟙 _ :=
  Iso.hom_inv_id _
