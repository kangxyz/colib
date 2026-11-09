/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteFibre

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : correspondenceLeftImageIncidence f g h i z w v)

example : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) ≃
    {y : correspondenceTripleIncidence f g h i z w v //
      correspondenceTripleToLeftImageIncidence f g h i z w v y = x} :=
  correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw

example (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v
        (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p).1 =
      correspondenceRemainingFiniteModelProjection f g h i z w v x
        ((correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm p).1 :=
  correspondenceRemainingFiniteMaximalEquivTriple_projection f g h i z w v x hz hw p

example (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))
      (p.asIdeal.comap (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))) p.asIdeal =
      (correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree
        (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p).1 :=
  primeResidueDegree_correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p

example : correspondenceRemainingFiniteClosedFibre f g h i z w v x ≃
    {q : correspondenceLeftIntermediateSupportProduct f g h i z w v //
      correspondenceLeftIntermediateImageMap f g h i z w v q =
        correspondenceLeftImageIncidenceInclusion f g h i z w v x} :=
  correspondenceRemainingFiniteClosedEquivExterior f g h i z w v x
