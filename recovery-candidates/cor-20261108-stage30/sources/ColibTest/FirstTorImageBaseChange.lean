/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.FirstTorImageBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Neither the finite map nor the exterior map is assumed flat for this actual sheaf identity.
example [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (n : ℕ) :
    (Scheme.Modules.pullback (correspondenceLeftImageExteriorProjection f g h i z w v)).obj
        (correspondencePairImageTorSheaf f g h z w n) ≅
      (Scheme.Modules.pushforward (correspondenceLeftIntermediateImageMap f g h i z w v)).obj
        (correspondenceLeftExteriorTorSheaf f g h i z w v n) :=
  correspondencePairImageTorSheafExteriorIso f g h i z w v hz hw n

#check Stacks.Chow.correspondenceLeftImageExteriorProjection
#check Stacks.Chow.correspondenceLeftIntermediateImageMap_projection
#check Stacks.Chow.correspondenceLeftIntermediateImageMap_isPullback
#check Stacks.Chow.isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
#check Stacks.Chow.length_correspondenceRemainingExteriorFiber_ne_top
#check Stacks.Chow.correspondencePairImageTorSheaf
#check Stacks.Chow.correspondencePairImageTorSheafExteriorIso
