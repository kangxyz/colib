/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteFibre

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    correspondenceRightRemainingFiniteClosedFibre f g h i z w v x ≃
      MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x) := by
  exact correspondenceRightRemainingFiniteClosedEquivMaximal
    f g h i z w v x hw hv

example
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    correspondenceTripleIncidenceToRightSupportProduct f g h i z w v
        (correspondenceRightRemainingFiniteMaximalEquivTriple f g h i z w v x hw hv p).1 =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x
        ((correspondenceRightRemainingFiniteClosedEquivMaximal
          f g h i z w v x hw hv).symm p).1 := by
  exact correspondenceRightRemainingFiniteMaximalEquivTriple_projection
    f g h i z w v x hw hv p

example
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x))
      (p.asIdeal.comap (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x))) p.asIdeal =
      (correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteMaximalEquivTriple f g h i z w v x hw hv p).1 := by
  exact primeResidueDegree_correspondenceRightRemainingFiniteMaximalEquivTriple
    f g h i z w v x hw hv p

end Stacks.Chow
