/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackStableOperation
public import Colib.KTheory.Waldhausen.Iterated.StableHomotopy

/-!
# Original nonnegative K-group operations of actual self-tracks

The proved stable operation is transported through the existing comparisons
with the unchanged original K-groups, including K-zero. This produces genuine
group homomorphisms, not only functions on object representatives. It does not
identify a scalar loop's object value or prove a localization boundary formula.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/SelfTrackKOperation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- The original comparison transports the actual degree-raising stable operation. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def originalKSelfTrackOperationAdd (H : Homotopy f f) (n : ℕ) :
    Additive (W.K n) →+ Additive (V.K (n + 1)) :=
  (originalKStableEquiv V (n + 1)).symm.toAddMonoidHom.comp
    ((H.stableOperation (n : ℤ)).hom.comp (originalKStableEquiv W n).toAddMonoidHom)

/-- Every original nonnegative K-group receives the genuine self-track homomorphism. -/
@[colib_tag "COL-0321", colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def originalKSelfTrackOperation (H : Homotopy f f) (n : ℕ) : W.K n →* V.K (n + 1) :=
  (originalKSelfTrackOperationAdd W V H n).toMultiplicative

/-- The operation retains the exact original stable comparison on every original K-class. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_stable (H : Homotopy f f) (n : ℕ) (a : W.K n) :
    originalKStableEquiv V (n + 1)
        (Additive.ofMul (originalKSelfTrackOperation W V H n a)) =
      H.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a)) := by
  exact (originalKStableEquiv V (n + 1)).apply_symm_apply _

/-- The unchanged stable comparison uniquely determines the operation on the original K-group. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_unique (H : Homotopy f f) (n : ℕ)
    (g : W.K n →* V.K (n + 1))
    (hg : ∀ a, originalKStableEquiv V (n + 1) (Additive.ofMul (g a)) =
      H.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a))) :
    g = originalKSelfTrackOperation W V H n := by
  ext a
  have h := (hg a).trans (originalKSelfTrackOperation_stable W V H n a).symm
  exact (originalKStableEquiv V (n + 1)).injective h

end CategoryTheory.Waldhausen.IteratedS
