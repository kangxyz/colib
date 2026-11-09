/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceEmpty

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (hne : Set.range (exteriorSupport_sourceProjection (SmoothSite.product X T)
    (SmoothSite.product X U)
    (nativeGraphComponent (SmoothSite.product X T) (SmoothSite.product X U)
      (SmoothSite.productMap (𝟙 X) ψ) t)) ≠
    Set.range (exteriorIdentitySource X Y T (integralComponentAt z)))

include hne

example :
    incidenceTorCorrespondence (SmoothSite.product X T).hom (SmoothSite.product X U).hom
      (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
      (nativeExteriorPoint X Y U z hz)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product X U).hom (SmoothSite.productMap (𝟙 X) ψ).left
        (MorphismProperty.Over.w _) t)
      (nativeExteriorPoint_admissible X Y U z hz) = 0 :=
  nativeMixedGraphIncidenceTor_eq_zero X Y T U ψ z hz t hne
