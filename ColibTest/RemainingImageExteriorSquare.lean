/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorFiberLength

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- No sheaf, smoothness, finite-type, or flatness hypothesis is needed for the full square.
example : IsPullback (correspondenceLeftExteriorProjection f g h i z w v)
    (correspondenceLeftIntermediateImageMap f g h i z w v)
    (correspondenceIncidenceMap f g h z w).toImage
    (correspondenceLeftImageExteriorProjection f g h i z w v) :=
  correspondenceLeftIntermediateImageMap_isPullback f g h i z w v

-- Finiteness of the actual map gives the needed full-source Noetherianity.
example [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v) :=
  isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
    f g h i z w v hz hw

#check correspondenceLeftImageExteriorProjection
#check correspondenceLeftIntermediateImageMap_projection
#check correspondenceLeftIntermediateImageMap_isPullback
#check isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
#check length_correspondenceRemainingExteriorFiber_ne_top
