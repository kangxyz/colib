/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOppositeRestriction
public import Colib.CategoryTheory.Waldhausen.WeakArrow.JointData

/-! # Actual opposite weak-arrow cylinders for perfect open restriction

The native perfect cylinder comparison discharges every component and coherence
input of the general opposite weak-arrow construction. Objects still store the
actual quasi-isomorphism from a restricted perfect complex to a target perfect
complex, and morphisms still store strictly commuting squares of chain maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- The literal opposite weak-arrow category for the existing perfect restriction functor. -/
def perfectComplexesRestrictWeakArrowOppositeWaldhausen :
    Waldhausen.Structure (WeakArrow.Obj (perfectComplexesWaldhausen Y.toRingedSpace)
      (perfectComplexesRestrictOpenImmersion j))ᵒᵖ :=
  WeakArrow.dualWaldhausenStructure
    (perfectComplexesWaldhausen X.toRingedSpace) (perfectComplexesWaldhausen Y.toRingedSpace)
    (perfectComplexesOppositeWaldhausen X.toRingedSpace)
    (perfectComplexesOppositeWaldhausen Y.toRingedSpace)
    (perfectComplexesRestrictOpenImmersion j)
    (perfectComplexesRestrictOpenImmersion_isExact j)
    (perfectComplexesRestrictOpenImmersion_op_exact j)
    (perfectComplexesOppositeWaldhausen_compatible Y.toRingedSpace)

/-- Genuine opposite weak-arrow joint data, with all component cylinders and endpoint
compatibility constructed on native perfect complexes rather than supplied as assumptions. -/
@[colib_tag "COL-0311",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/JointData.lean:41-56" "specialization"
    "All original component-joint and endpoint inputs are discharged for native perfect \
    open restriction"]
def perfectComplexesRestrictWeakArrowOppositeJointData :
    Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl
      (perfectComplexesRestrictWeakArrowOppositeWaldhausen j)) :=
  WeakArrow.dualJointData
    (perfectComplexesWaldhausen X.toRingedSpace) (perfectComplexesWaldhausen Y.toRingedSpace)
    (perfectComplexesOppositeWaldhausen X.toRingedSpace)
    (perfectComplexesOppositeWaldhausen Y.toRingedSpace)
    (perfectComplexesRestrictOpenImmersion j)
    (perfectComplexesRestrictOpenImmersion_isExact j)
    (perfectComplexesRestrictOpenImmersion_op_exact j)
    (perfectComplexesOppositeWaldhausen_compatible Y.toRingedSpace)
    (perfectComplexesOppositeJointData X.toRingedSpace)
    (perfectComplexesOppositeJointData Y.toRingedSpace)
    (perfectComplexesRestrictOpenImmersionJointIso j)
    (perfectComplexesRestrictOpenImmersionJointIso_inv_inl j)
    (perfectComplexesRestrictOpenImmersionJointIso_inv_inr j)
    (perfectComplexesRestrictOpenImmersionJointIso_inv_projection j)

end AlgebraicGeometry.Scheme.Modules
