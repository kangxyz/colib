module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingOriginalList

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Finite colength is derived from actual geometry, not supplied as a premise.
example [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (hs : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList s) :
    IsIdealOfDefinition (Ideal.span (Set.range
      (s.map (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1)).get)) :=
  isIdealOfDefinition_correspondenceRemainingOriginalList f g h i z w v x s hs
