/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteFibre
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericImageSupport

/-!
# All right finite-algebra maximal labels are actual generic triple-fibre labels

Above a generic right-image incidence point, every point of the actual finite fibre is
generic. Restrict the actual full-fibre equivalence without changing its point, germ prime,
or original residue degree. No genericity dictionary or reduced replacement is an input.
References: native quasi-finite discrete fibres and Stacks 02R4.
-/

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

/-- Every point in the actual finite right fibre above a generic point is generic. -/
theorem mem_genericPoints_correspondenceRightRemainingTripleFibre [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v))
    (y : correspondenceRightRemainingTripleFibre f g h i z w v x) :
    y.1 ∈ genericPoints (correspondenceTripleIncidence f g h i z w v) := by
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  exact mem_genericPoints_of_finite_image
    (correspondenceTripleToRightImageIncidence f g h i z w v) y.1 (y.2.symm ▸ hx)

/-- Every maximal ideal retains its actual generic triple point in the right fibre. -/
def correspondenceRightRemainingFiniteMaximalEquivGenericTriple [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x) ≃
      {y : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToRightImageIncidence f g h i z w v y.1 = x} :=
  (correspondenceRightRemainingFiniteMaximalEquivTriple f g h i z w v x hw hv).trans
    { toFun := fun y => ⟨⟨y.1,
        mem_genericPoints_correspondenceRightRemainingTripleFibre
          f g h i z w v hw hv x hx y⟩, y.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The actual prime degree equals the original right triple-to-image degree at the same label. -/
theorem primeResidueDegree_correspondenceRightRemainingFiniteMaximalEquivGenericTriple
    [IsSeparated i]
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
          f g h i z w v hw hv x hx p).1.1 :=
  primeResidueDegree_correspondenceRightRemainingFiniteMaximalEquivTriple
    f g h i z w v x hw hv p

end Stacks.Chow
