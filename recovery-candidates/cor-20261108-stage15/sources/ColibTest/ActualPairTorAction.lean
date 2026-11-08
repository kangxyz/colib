/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorAction

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  [IsSeparated g] (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w) (n : ℕ)

example : RingHom.ker ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom ≤
    Module.annihilator (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientTor f g h z w x n) :=
  correspondenceIncidence_ker_le_annihilator_tor f g h z w x n

example (a : correspondenceIncidenceAmbientStalk f g h z w x)
    (m : correspondenceIncidenceAmbientTor f g h z w x n) :
    letI := correspondenceIncidenceTorModule f g h z w x n
    ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom a • m = a • m :=
  correspondenceIncidenceTorModule_stalkMap_smul f g h z w x n a m

example :
    letI := correspondenceIncidenceTorModule f g h z w x n
    Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientTor f g h z w x n) =
        Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
          (correspondenceIncidenceAmbientTor f g h z w x n) :=
  correspondenceIncidenceTor_length_eq_incidence f g h z w x n
