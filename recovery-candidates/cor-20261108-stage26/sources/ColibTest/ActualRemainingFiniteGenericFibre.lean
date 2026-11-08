/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteGenericFibre

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open TopologicalSpace

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : correspondenceLeftImageIncidence f g h i z w v)
  (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v))

example : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) ≃
    {y : genericPoints (correspondenceTripleIncidence f g h i z w v) //
      correspondenceTripleToLeftImageIncidence f g h i z w v y.1 = x} :=
  correspondenceRemainingFiniteMaximalEquivGenericTriple f g h i z w v hz hw x hx

example (y : correspondenceRemainingTripleFibre f g h i z w v x) :
    y.1 ∈ genericPoints (correspondenceTripleIncidence f g h i z w v) :=
  mem_genericPoints_correspondenceRemainingTripleFibre f g h i z w v hz hw x hx y

example (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    (correspondenceRemainingFiniteMaximalEquivGenericTriple f g h i z w v hz hw x hx p).1.1 =
      (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p).1 :=
  correspondenceRemainingFiniteMaximalEquivGenericTriple_val f g h i z w v hz hw x hx p
