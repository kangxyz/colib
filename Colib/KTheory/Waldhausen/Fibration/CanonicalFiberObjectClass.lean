/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberObjectLoop
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup

/-! # Canonical fiber maps on actual object classes

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarForwardRelativeBoundary.lean:121-134`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The proof uses only the native
Waldhausen object class and actual canonical fiber loop, so it belongs at their generic owner.
Independent category universes and the original chosen basepoints are retained.
-/

@[expose] public noncomputable section
open CategoryTheory Topology HomotopyGroup
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original canonical-fiber K-map sends the original object class to its actual fiber loop. -/
theorem canonicalFiberKMap_object (A : AcyclicCategory N) :
    canonicalFiberKMap N 0
      ((acyclicStructure N).kZeroObjectClass A) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      ((FundamentalGroup.fromPath ⟦canonicalFiberObjectLoop N A⟧) : FundamentalGroup _
        (HomotopyFiber.basepoint _ _ _ (changeWeakMap_basepoint _))) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (piMap 0 (canonicalFiberMap N) (canonicalFiberMap_basepoint _)
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath ⟦(acyclicStructure N).kZeroObjectLoop A⟧))) = _
  rw [HomotopyGroup.mapHom_apply, HomotopyGroup.pi1MulEquivFundamentalGroup_naturality,
    MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarForwardRelativeBoundary.lean:121-134"
  "adaptation" "The actual canonical fiber K-map sends the original acyclic object class to
    its literal fiber loop; the proof is generic in independent object and morphism universes"]
  canonicalFiberKMap_object

end CategoryTheory.Waldhausen.Fibration
