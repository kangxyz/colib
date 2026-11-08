module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

-- No field, connectedness or integrality hypothesis is needed for ambient flatness.
example [Flat g] : Flat (correspondenceRemainingProjection f g h i) := inferInstance

-- No flatness assumption is imposed on the finite original-to-image map.
example [IsSeparated h]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceTripleToLeftImageIncidence f g h i z w v) :=
  isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw

end
