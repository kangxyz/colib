/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorZero

/-! # Actual degree-zero pair Tor, without regularity or flatness providers -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  [IsSeparated g] (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w)

example : correspondenceIncidenceAmbientTor f g h z w x 0 ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom).obj
      (ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk x)
        ((correspondenceIncidence f g h z w).presheaf.stalk x)) :=
  correspondenceIncidenceAmbientTorZeroIso f g h z w x

example : Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
    (correspondenceIncidenceAmbientTor f g h z w x 0) =
      Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
        ((correspondenceIncidence f g h z w).presheaf.stalk x) :=
  length_correspondenceIncidenceAmbientTor_zero f g h z w x

example :
    letI := correspondenceIncidenceTorSupportModule f g h z w x 0
    Module.length ((correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x))
      (correspondenceIncidenceAmbientTor f g h z w x 0) =
        Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
          ((correspondenceIncidence f g h z w).presheaf.stalk x) :=
  length_correspondenceIncidenceAmbientTor_zero_support f g h z w x
