/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleFirstStageAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S) [IsSeparated g]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)

example : RingHom.ker (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x) =
    correspondenceTripleIncidenceFirstStageStalkIdeal f g h i z w v x :=
  correspondenceTripleIncidenceFirstStageStalkMap_ker f g h i z w v x

example (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    (m : (Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) :
    letI := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t hr ht n
    correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x a • m = a • m :=
  correspondenceTripleIncidenceFirstKoszulModule_stalkMap_smul f g h i z w v x t hr ht n a m
