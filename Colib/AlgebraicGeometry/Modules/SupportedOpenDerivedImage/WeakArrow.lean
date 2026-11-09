/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.JointComparison
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
namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
universe u d
variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j T)]

/-- The literal opposite weak-arrow category for the existing perfect restriction functor. -/
def weakArrowOppositeWaldhausen :
    Waldhausen.Structure (WeakArrow.Obj (waldhausen j T Fact.out)
      (corestrict j T))ᵒᵖ :=
  WeakArrow.dualWaldhausenStructure
    (perfectSupportedWaldhausen T.ι) (waldhausen j T Fact.out)
    (perfectSupportedOppositeWaldhausen T.ι)
    (oppositeWaldhausen j T)
    (corestrict j T)
    (corestrict_isExact j T Fact.out)
    (corestrict_op_isExact j T)
    (oppositeWaldhausen_compatible j T)

/-- Genuine opposite weak-arrow joint data, with all component cylinders and endpoint
compatibility constructed on native perfect complexes rather than supplied as assumptions. -/
def weakArrowOppositeJointData :
    Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl
      (weakArrowOppositeWaldhausen j T)) :=
  WeakArrow.dualJointData
    (perfectSupportedWaldhausen T.ι) (waldhausen j T Fact.out)
    (perfectSupportedOppositeWaldhausen T.ι)
    (oppositeWaldhausen j T)
    (corestrict j T)
    (corestrict_isExact j T Fact.out)
    (corestrict_op_isExact j T)
    (oppositeWaldhausen_compatible j T)
    (perfectSupportedOppositeJointData T.ι)
    (oppositeJointData j T)
    (corestrictJointIso j T)
    (corestrictJointIso_inv_inl j T)
    (corestrictJointIso_inv_inr j T)
    (corestrictJointIso_inv_projection j T)

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
