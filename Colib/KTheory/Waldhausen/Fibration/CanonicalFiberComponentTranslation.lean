/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberObjectPrefixTransport
public import Colib.Topology.HomotopyFiber.SquareEquivalence
public import Colib.Topology.HomotopyFiber.PointComparison

/-!
# The prescribed canonical-fiber component translation

The original strict left-concatenation square consists of genuine homotopy equivalences.
Its existing fiber equivalence followed by the actual identity-cofiber suffix therefore
supplies a genuine equivalence with the previously constructed canonical-fiber translation
as its literal value. Both the original source loop and entire reversed fiber path survive.

Implementation provenance: all five declarations of
`Quillen/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The strict square, genuine equivalences,
identity-cofiber suffix and literal object values retain the original definitions. Only the
suffix/component section needs zero morphisms; the category universes remain independent.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (A : C)

/-- The original object-loop prefixes commute with the unchanged localization loop map. -/
theorem canonicalFiberPrefix_square :
    (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)).toFun.comp
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)) =
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)).comp
        (loopLeftTranslationEquiv (V.kZeroObjectLoop A)).toFun := by
  have hA : basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
      (V.kZeroObjectLoop A) = N.coarse.kZeroObjectLoop A :=
    deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A
  have hs := loopLeftTranslationEquiv_naturality
    (changeWeakMap N) (changeWeakMap_basepoint N) (V.kZeroObjectLoop A)
  rw [hA] at hs
  exact hs.symm

/-- The actual prefix map is a genuine equivalence on the original localization loop fibers. -/
def canonicalFiberPrefixEquiv :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (Path.refl N.coarse.kBasepoint))
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))) :=
  (HomotopyFiber.mapHomotopyEquivOfEquivalences
    (loopLeftTranslationEquiv (V.kZeroObjectLoop A))
    (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A))
    (canonicalFiberPrefix_square N A) (Path.refl N.coarse.kBasepoint)).trans
      (HomotopyFiber.basepointEqHomeomorph
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (loopLeftTranslationEquiv_apply (N.coarse.kZeroObjectLoop A)
          (Path.refl N.coarse.kBasepoint))).toHomotopyEquiv

/-- Its forward map on the original transposed object loop is exactly the previously defined point.
-/
theorem canonicalFiberPrefixEquiv_object (X : AcyclicCategory N) :
    canonicalFiberPrefixEquiv N A (canonicalFiberObjectLoopTranspose N X) =
      canonicalFiberObjectPrefixed N A X := by
  apply Subtype.ext
  refine _root_.Prod.ext ?_ ?_
  · change loopLeftTranslationEquiv (V.kZeroObjectLoop A)
      (canonicalFiberObjectLoopTranspose N X).val.1 = _
    rw [canonicalFiberObjectLoopTranspose_source, loopLeftTranslationEquiv_apply]
    rfl
  · rfl

variable [HasZeroMorphisms C]

/-- The entire prescribed prefix and identity-triangle transport is a genuine fiber equivalence. -/
def canonicalFiberComponentEquiv :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (Path.refl N.coarse.kBasepoint))
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (N.coarse.kZeroObjectLoop A)) :=
  (canonicalFiberPrefixEquiv N A).trans
    (HomotopyFiber.basepointTransportEquiv
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (N.coarse.identityCofiberSuffixPath A))

/-- The original canonical-fiber point retains its exact prescribed full translation. -/
theorem canonicalFiberComponentEquiv_object (X : AcyclicCategory N) :
    canonicalFiberComponentEquiv N A (canonicalFiberObjectLoopTranspose N X) =
      canonicalFiberObjectPrefixTransport N A X := by
  change HomotopyFiber.basepointTransportEquiv _ _
    (canonicalFiberPrefixEquiv N A (canonicalFiberObjectLoopTranspose N X)) = _
  rw [canonicalFiberPrefixEquiv_object]
  rfl

attribute [colib_tag "COL-0296"] canonicalFiberPrefixEquiv
  canonicalFiberPrefixEquiv_object canonicalFiberComponentEquiv canonicalFiberComponentEquiv_object

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean:31-94" "adaptation"
  "The strict left-translation square, genuine prefix and prescribed identity-cofiber suffix
    equivalences, and both literal transposed canonical-object values; independent category
    universes and the original zero-morphism section cut are retained"]
  canonicalFiberPrefix_square canonicalFiberPrefixEquiv canonicalFiberPrefixEquiv_object
  canonicalFiberComponentEquiv canonicalFiberComponentEquiv_object

end CategoryTheory.Waldhausen.Fibration
