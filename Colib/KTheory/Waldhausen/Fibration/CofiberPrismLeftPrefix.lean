/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.CofiberPrismFiber
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.LeftComponentTranslation

/-!
# The original canonical-fiber loop and its exact source prefix

The existing loop/fiber homeomorphism transposes the two original coordinates. Left translation
then gives exactly the source prefix in the cofiber prism, retaining the original reversed
canonical-fiber path. The component equivalence uses the prescribed suffix-removal path; no
arbitrary path between components or Laurent boundary identity is introduced.
-/
/-! Implementation provenance: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Only `cofiberPrismCompositionCube_zero_leftPrefix` from
`Quillen/Waldhausen/Fibration/CofiberPrismLeftPrefix.lean:56-65`.
The existing native transpose is imported, not duplicated or reversed a second time.
Independent category universes and all original hypotheses are preserved.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Topology unitInterval
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

section Cofiber
variable [HasZeroMorphisms C] {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : N.coarse.cof i) (hwi : N.coarse.weq i)
  (hQ : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- Left translation of the actual transposed fiber path is the literal cofiber-prism prefix. -/
theorem cofiberPrismCompositionCube_zero_leftPrefix (s t : unitInterval) :
    loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)
        ((canonicalFiberObjectLoopTranspose N
          (cofiberPrismAcyclicQuotient N i q hi hwi hQ)).val.2 s)
        t =
      N.coarse.cofiberPrismCompositionCube i q hi hwi hQ (0, unitInterval.symm s, t) := by
  rw [loopLeftTranslationEquiv_apply, Path.trans_apply,
    cofiberPrismCompositionCube_zero_fiber N i q hi hwi hQ]
  split_ifs <;> rfl

end Cofiber

attribute [colib_tag "COL-0297"] cofiberPrismCompositionCube_zero_leftPrefix

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/CofiberPrismLeftPrefix.lean:56-65" "adaptation"
  "The actual transposed canonical-fiber path after source prefixing equals the entire
    comparison-zero cofiber cube at reversed nerve time; transposition adds no second reversal"]
  cofiberPrismCompositionCube_zero_leftPrefix

end CategoryTheory.Waldhausen.Fibration
