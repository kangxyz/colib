/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CoarseJoint

/-! # Genuine retargeting of original fine joint data

The original endpoints and weak projection are unchanged. Coarse exactness is
derived through the actual coarse gluing and two-out-of-three argument.

Implementation provenance: `Quillen/Waldhausen/Fibration/Rows/JointRetarget.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual maps, structural hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen

namespace Fibration.RowFactorization
variable {C : Type u} [Category.{v} C] {W : Structure C}
  (J : JointData (NestedWeakEquivalences.refl W)) (N : NestedWeakEquivalences W)

/-- A fine-weak actual projection also supplies the nested weak-class input. -/
def JointData.toNested : JointData N where
  joint := J.joint
  exact := J.exact
  inl := J.inl
  inr := J.inr
  coproduct := J.coproduct
  projection := J.projection
  factorization := J.factorization
  weak f := N.le_weq _ (J.weak f)

/-- Fine joint data yields a genuinely coarse-exact joint functor by the proved
coarse gluing and two-out-of-three argument, with unchanged endpoints. -/
def JointData.toCoarse [N.coarse.weq.HasTwoOutOfThreeProperty] :
    JointData (NestedWeakEquivalences.refl N.coarse) :=
  (J.toNested N).coarseReflexive N

@[simp] theorem JointData.toCoarse_projection [N.coarse.weq.HasTwoOutOfThreeProperty]
    (f : Arrow C) : (J.toCoarse N).projection.app f = J.projection.app f := rfl

@[simp] theorem JointData.toCoarse_inl [N.coarse.weq.HasTwoOutOfThreeProperty]
    (f : Arrow C) : (J.toCoarse N).inl.app f = J.inl.app f := rfl

@[simp] theorem JointData.toCoarse_inr [N.coarse.weq.HasTwoOutOfThreeProperty]
    (f : Arrow C) : (J.toCoarse N).inr.app f = J.inr.app f := rfl

end Fibration.RowFactorization
end CategoryTheory.Waldhausen
