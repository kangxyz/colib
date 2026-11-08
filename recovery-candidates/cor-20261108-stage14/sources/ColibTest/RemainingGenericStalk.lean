module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingGenericStalk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- No reducedness, integrality, equidimensionality or caller-supplied colength hypothesis.
example [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    IsArtinianRing (correspondenceRemainingOriginalStalk f g h i z w v x.1 ⧸
      correspondenceRemainingOriginalStalkIdeal f g h i z w v x.1) :=
  isArtinianRing_correspondenceRemainingOriginalStalkQuotient f g h i z w v x

example [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    IsIdealOfDefinition (correspondenceRemainingOriginalStalkIdeal f g h i z w v x.1) :=
  isIdealOfDefinition_correspondenceRemainingOriginalStalkIdeal f g h i z w v x
