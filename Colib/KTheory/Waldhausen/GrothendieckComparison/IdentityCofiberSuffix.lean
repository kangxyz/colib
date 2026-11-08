/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberObjectTrack

/-!
# The specified identity-cofiber suffix path

The identity cofibration has its literal chosen-zero quotient. Its actual affine
triangle track removes the displayed constant suffix from the canonical object loop.
Both triangle time and loop time are retained.

Implementation provenance: only `identityCofiberSuffixPath` and
`identityCofiberSuffixPath_apply` from
`Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean`, lines 32–60,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The generic component equivalence and
localization naturality from that file are not included.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.QuotientRows
open scoped Topology Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- The original identity-cofiber triangle removes the literal chosen-zero suffix. -/
def identityCofiberSuffixPath :
    Path ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)) (W.kZeroObjectLoop A) where
  toFun s := {
    toFun t := W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W) (s, t)
    continuous_toFun := by fun_prop
    source' := Path.Homotopy.source _ s
    target' := Path.Homotopy.target _ s }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W)).continuous
  source' := by
    ext t
    change W.cofiberObjectLoopTrack _ _ _ _ (0, t) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    change ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop W.zero)) t = _
    rw [W.kZeroObjectLoop_zero]
  target' := by
    ext t
    exact (W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W)).apply_one t

/-- Both original triangle comparison and object-loop coordinates remain unchanged. -/
theorem identityCofiberSuffixPath_apply (s t : unitInterval) :
    W.identityCofiberSuffixPath A s t =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (s, t) := rfl

end CategoryTheory.Waldhausen.Structure
