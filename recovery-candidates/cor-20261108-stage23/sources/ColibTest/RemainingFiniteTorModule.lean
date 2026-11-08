/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorModule

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]

-- No arbitrary module family or finite-generation hypothesis is an input.
example (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) (n : ℕ) :
    Module.Finite (correspondenceRemainingFiniteRing f g h i z w v x)
      (correspondenceRemainingFiniteTorModule f g h i z w v x n) :=
  moduleFinite_correspondenceRemainingFiniteTorModule f g h i z w v hz hw x n

end

#check Stacks.Chow.correspondenceLeftExteriorTorSheaf

#check Stacks.Chow.correspondenceRemainingFiniteTorSheaf

#check Stacks.Chow.correspondenceRemainingFiniteTorModule

#check Stacks.Chow.isQuasicoherent_isFiniteType_correspondenceLeftExteriorTorSheaf

#check Stacks.Chow.isQuasicoherent_isFiniteType_correspondenceRemainingFiniteTorSheaf

#check Stacks.Chow.moduleFinite_correspondenceRemainingFiniteTorModule

#check Stacks.Chow.sheafMultiplicity_correspondenceLeftExteriorTorSheaf

#check Stacks.Chow.length_correspondenceRemainingFiniteTorKoszul_ne_top

#check Stacks.Chow.sum_signed_seqEuler_correspondenceRemainingFiniteTorModule
