/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingPrimeTorImageLabel

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : correspondenceLeftImageIncidence f g h i z w v)

example (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    correspondenceRemainingImagePrime f g h i z w v x
        (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x q).1 =
      correspondenceRemainingFiniteModelStructure f g h i z w v x q.1 :=
  correspondenceRemainingImagePrime_eq_modelStructure f g h i z w v hz hw x q

example (η : correspondenceRemainingOriginalGenericLabels f g h i z w v x) :
    correspondenceRemainingImagePrimeClosure f g h i z w v x
      (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x
        ((correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x).symm η)).1 =
        integralComponentAt (correspondenceLeftIntermediateImageMap f g h i z w v η.1.1) :=
  correspondenceRemainingImagePrimeClosure_eq_originalLabel f g h i z w v hz hw x η
