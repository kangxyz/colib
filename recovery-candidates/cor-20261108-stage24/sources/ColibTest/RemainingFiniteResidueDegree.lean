module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteResidueDegree

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) =
      ((Scheme.ΓSpecIso (correspondenceRemainingImageStalk f g h i z w v x)).inv ≫
        (correspondenceRemainingFiniteModelStructure f g h i z w v x).appTop).hom :=
  correspondenceRemainingFiniteAlgebra_algebraMap f g h i z w v x

#check correspondenceRemainingFiniteAlgebra_algebraMap
#check primeResidueDegree_correspondenceRemainingFiniteModel

end Stacks.Chow
