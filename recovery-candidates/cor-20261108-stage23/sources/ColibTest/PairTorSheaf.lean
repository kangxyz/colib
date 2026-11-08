/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

noncomputable section

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h) [IsSeparated g]

-- The literal full-incidence action is compared without a regular-list witness.
example (x : correspondenceIncidence f g h z w) (n : ℕ) :
    letI := correspondenceIncidenceTorModule f g h z w x n
    AlgebraicGeometry.TorFormula.stalkModuleCat (correspondenceIncidence f g h z w)
        (correspondencePairTorSheaf f g h z w n) x ≅
      ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk x)
        (correspondenceIncidenceAmbientTor f g h z w x n) :=
  correspondencePairTorSheafStalkIso f g h z w x n

example (x : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
        ((correspondencePairTorSheaf f g h z w n).presheaf.stalk x) =
      Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
        (correspondenceIncidenceAmbientTor f g h z w x n) :=
  length_correspondencePairTorSheaf_stalk f g h z w x n

end

#check Stacks.Chow.correspondencePairSupportSheaf

#check Stacks.Chow.correspondencePairDiagonalSheaf

#check Stacks.Chow.correspondencePairAmbientTorSheaf

#check Stacks.Chow.correspondencePairTorSheaf

#check Stacks.Chow.isCoherent_correspondencePairAmbientTorSheaf

#check Stacks.Chow.isQuasicoherent_isFiniteType_correspondencePairTorSheaf

#check Stacks.Chow.correspondencePairAmbientTorSheafStalkIso

#check Stacks.Chow.correspondencePairTorSheafStalkIso

#check Stacks.Chow.length_correspondencePairTorSheaf_stalk

#check Stacks.Chow.correspondencePairAmbientTorSheafStalk_ker_le_annihilator
