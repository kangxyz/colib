/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphPrimes

/-!
# In-package checks for native exterior GraphPrimes
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] (φ : X ⟶ Y) (t : genericPoints X.left)

example : (exteriorIdentityInclusion X Y T (nativeGraphComponent X Y φ t)).ker =
    nativeGraphComponent (SmoothSite.product X T) (SmoothSite.product Y T)
      (SmoothSite.productMap φ (𝟙 T)) (exteriorSourceGenericsEquiv X T t) :=
  nativeExteriorImage_eq_productGraphComponent X Y T φ t

example : nativeExteriorPrime X Y T
    (correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) t.val)
    (isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) t) =
    singleFiniteCorrespondence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (correspondenceGraphMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.productMap φ (𝟙 T)).left (MorphismProperty.Over.w _)
        (exteriorSourceGenericsEquiv X T t).val)
      (isFiniteCorrespondencePoint_graphMap (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w _) (exteriorSourceGenericsEquiv X T t)) 1 :=
  nativeExteriorPrime_graph X Y T φ t
