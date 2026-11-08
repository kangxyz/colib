module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageGenericStalk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The full intermediate image, with no caller-supplied finite-colength hypothesis.
example [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    IsIdealOfDefinition (Ideal.span (Set.range (fun j =>
      correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1 (s j)))) :=
  isIdealOfDefinition_correspondenceRemainingImageMiddleList f g h i z w v x s hs
