/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteGenericFibre

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x) ≃
      {y : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToRightImageIncidence f g h i z w v y.1 = x} := by
  exact correspondenceRightRemainingFiniteMaximalEquivGenericTriple
    f g h i z w v hw hv x hx

example
    [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v))
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree (algebraMap R B)
      (p.asIdeal.comap (algebraMap R B)) p.asIdeal =
      (correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteMaximalEquivGenericTriple
          f g h i z w v hw hv x hx p).1.1 := by
  exact primeResidueDegree_correspondenceRightRemainingFiniteMaximalEquivGenericTriple
    f g h i z w v hw hv x hx p

end Stacks.Chow
