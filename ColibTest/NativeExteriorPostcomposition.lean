/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Postcomposition

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow Function.locallyFinsuppWithin
attribute [local instance] isIntegral_integralComponentAt
universe u
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

example : nativeExteriorPrime X Y T z hz =
    singleFiniteCorrespondence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint_admissible X Y T z hz) 1 :=
  nativeExteriorPrime_eq_single X Y T z hz

open Classical in
example
    (Z : SmoothSite (Spec (.of k))) (ψ : SmoothSite.product Y T ⟶ Z) :
    (incidenceTorPairing (SmoothSite.product X T).hom (SmoothSite.product Y T).hom Z.hom
      (nativeExteriorPrime X Y T z hz)
      (graphCorrespondenceOfComponents (SmoothSite.product Y T).hom Z.hom ψ.left
        (MorphismProperty.Over.w ψ)
        (Cor.finite_genericPoints k (Cor.mk (SmoothSite.product Y T))))).val =
      letI := isFinite_correspondenceGraphPostcompositionMap
        (SmoothSite.product X T).hom (SmoothSite.product Y T).hom Z.hom ψ.left
        (MorphismProperty.Over.w ψ) (nativeExteriorPoint X Y T z hz)
        (nativeExteriorPoint_admissible X Y T z hz)
      finiteCyclePushforward
        (correspondenceGraphPostcompositionMap (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom Z.hom ψ.left (MorphismProperty.Over.w ψ)
          (nativeExteriorPoint X Y T z hz))
        (single (genericPoint (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme)
          1) :=
  nativeExteriorPrime_graph_right_val X Y T z hz Z ψ
