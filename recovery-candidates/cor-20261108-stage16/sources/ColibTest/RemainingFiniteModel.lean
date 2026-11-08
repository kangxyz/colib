module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)


example [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Module.Finite (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) :=
  moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x

#check correspondenceRemainingFiniteModel
#check correspondenceRemainingFiniteModelProjection
#check correspondenceRemainingFiniteModelStructure
#check correspondenceRemainingFiniteRing
#check correspondenceRemainingFiniteAlgebra
#check isFinite_correspondenceRemainingFiniteModelStructure
#check isAffine_correspondenceRemainingFiniteModel
#check moduleFinite_correspondenceRemainingFiniteRing
#check finite_maximalSpectrum_correspondenceRemainingFiniteRing
#check flat_correspondenceRemainingFiniteModelProjection
#check isIso_correspondenceRemainingFiniteModelProjection_stalkMap
#check correspondenceRemainingFiniteGenericLabel
#check residueDegree_correspondenceRemainingFiniteModelStructure

end Stacks.Chow
