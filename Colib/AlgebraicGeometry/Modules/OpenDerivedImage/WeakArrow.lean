/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.JointComparison
public import Colib.CategoryTheory.Waldhausen.WeakArrow.JointData

/-! # Actual opposite weak-arrow cylinders for honest-image corestriction

The native perfect cylinder comparison discharges every component and coherence
input of the general opposite weak-arrow construction. Objects still store the
actual quasi-isomorphism from a restricted perfect complex to a target honest-image
complex, and morphisms still store strictly commuting squares of chain maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace
namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
universe u d
variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]

/-- The literal opposite weak-arrow category for the existing perfect restriction functor. -/
def weakArrowOppositeWaldhausen :
    Waldhausen.Structure (WeakArrow.Obj (waldhausen j Fact.out)
      (corestrict j))ᵒᵖ :=
  WeakArrow.dualWaldhausenStructure
    (perfectComplexesWaldhausen X.toRingedSpace) (waldhausen j Fact.out)
    (perfectComplexesOppositeWaldhausen X.toRingedSpace)
    (oppositeWaldhausen j)
    (corestrict j)
    (corestrict_isExact j Fact.out)
    (corestrict_op_isExact j)
    (oppositeWaldhausen_compatible j)

/-- Genuine opposite weak-arrow joint data, with all component cylinders and endpoint
compatibility constructed on native perfect complexes rather than supplied as assumptions. -/
@[colib_tag "COL-0314",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/JointData.lean:28-35"
    "adaptation"
    "All original component-joint and endpoint inputs are discharged for native honest-image \
    corestriction given the geometric roof property"]
def weakArrowOppositeJointData :
    Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl
      (weakArrowOppositeWaldhausen j)) :=
  WeakArrow.dualJointData
    (perfectComplexesWaldhausen X.toRingedSpace) (waldhausen j Fact.out)
    (perfectComplexesOppositeWaldhausen X.toRingedSpace)
    (oppositeWaldhausen j)
    (corestrict j)
    (corestrict_isExact j Fact.out)
    (corestrict_op_isExact j)
    (oppositeWaldhausen_compatible j)
    (perfectComplexesOppositeJointData X.toRingedSpace)
    (oppositeJointData j)
    (corestrictJointIso j)
    (corestrictJointIso_inv_inl j)
    (corestrictJointIso_inv_inr j)
    (corestrictJointIso_inv_projection j)

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
