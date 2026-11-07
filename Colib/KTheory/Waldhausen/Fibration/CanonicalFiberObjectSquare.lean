/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberObjectLoop
public import Colib.KTheory.Waldhausen.ObjectTransformationTrack
public import Colib.KTheory.Waldhausen.ObjectTransformationSquareRealization

/-!
# The original reversed weak-square coordinate in the canonical fiber

The fiber coordinate is the actual zero-to-acyclic component square, with its nerve parameter
reversed and its object-loop parameter unchanged. This is an equality of the specified family.
A later Laurent application must match the original coordinate unit and its actual loop orientation;
the cofiber sign isomorphism alone does not establish that comparison.
-/
/-! Implementation provenance: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Selected original declarations from `Quillen/Waldhausen/Fibration/`:
* `CanonicalFiberObjectLoop.lean:63-76`: the acyclic transformation and its reversal.
* `CanonicalFiberObjectSquare.lean:30-47`: the entire specified component square.
The seven pending native loop/transpose declarations are imported unchanged.
Independent category universes and all original hypotheses are preserved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology Convexity
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original zero-to-acyclic exact-functor cylinder evaluated at the actual object loop. -/
def acyclicObjectTransformationTrack (X : AcyclicCategory N) :
    (N.coarse.kZeroObjectLoop N.coarse.zero).Homotopy (N.coarse.kZeroObjectLoop X.obj) :=
  objectTransformationTrack (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) rfl
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) X

/-- The actual canonical fiber coordinate is exactly the original transformation track reversed.
-/
theorem canonicalFiberObjectLoop_path_transformation (X : AcyclicCategory N)
    (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      acyclicObjectTransformationTrack N X (unitInterval.symm s, t) := rfl

/-- The full fiber path uses the original component square at the reversed nerve coordinate. -/
theorem canonicalFiberObjectLoop_path_square (X : AcyclicCategory N)
    (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      bisimplexRealization N.coarse
        (N.coarse.weakObjectSimplex ((zeroToAcyclicInclusion N).app X)
          (zeroToAcyclicInclusion_weak N X)).val
        ((isSimplex₂_diagonal_iff N.coarse.cof N.coarse.weq _).mpr
          (N.coarse.weakObjectSimplex ((zeroToAcyclicInclusion N).app X)
            (zeroToAcyclicInclusion_weak N X)).property)
        (StdSimplex.homeomorphI.symm t,
          StdSimplex.homeomorphI.symm (unitInterval.symm s)) := by
  rw [canonicalFiberObjectLoop_path_transformation]
  exact objectTransformationRealization_square (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) rfl
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) X
    (unitInterval.symm s) t

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/CanonicalFiberObjectLoop.lean:63-76" "adaptation"
  "The selected zero-to-acyclic transformation track and the exact reversed canonical-fiber
    coordinate; the existing loop and transpose definitions are reused without duplication"]
  acyclicObjectTransformationTrack canonicalFiberObjectLoop_path_transformation

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/CanonicalFiberObjectSquare.lean:30-47" "adaptation"
  "Equality with the whole realized zero-to-acyclic component square, including its mixed
    maps and strict chosen-zero equalities; fiber time is reversed and loop time is unchanged"]
  canonicalFiberObjectLoop_path_square

end CategoryTheory.Waldhausen.Fibration
