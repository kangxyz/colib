/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleCoefficientTotal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)
  (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))

example : correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s ≅
    correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s :=
  correspondenceTripleIncidenceTwoListIsoRemainingTotal f g h i z w v x t s

example (n : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      ((correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s).homology n) =
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      ((correspondenceTripleIncidenceRemainingTotal f g h i z w v x t s).homology n) :=
  correspondenceTripleIncidenceTwoList_length_eq_remainingTotal f g h i z w v x t s n
