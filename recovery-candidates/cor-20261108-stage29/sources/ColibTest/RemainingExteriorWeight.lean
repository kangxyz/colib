/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorWeight

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

-- No global equidimensionality or reduction of either exterior scheme is assumed.
example {S X Y Z W : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i) (C : ChowSituation.{u})
    (sE : correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶ C.S)
    [LocallyOfFiniteType sE]
    (η : genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v)) :
    flatPullbackWeight C sE (correspondenceLeftExteriorProjection f g h i z w v)
        (relativeDimension C.dimensionFunction sE η.1) η.1 =
      (correspondenceLeftExteriorFiberLength f g h i z w v η.1 : ℤ) :=
  flatPullbackWeight_correspondenceLeftExterior_generic f g h i z w v C sE η

#check exists_correspondenceExteriorGeneric_comap
#check flatPullbackWeight_correspondenceLeftExterior_generic
#check flatPullbackWeight_correspondenceLeftExterior_generic_grade
