/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Colib.KTheory.Waldhausen.WeakNaturalTransformationBased

/-!
# Original transformation cylinders on actual object loops

Evaluation of the unchanged realization homotopy gives an endpoint-relative, data-valued
object-loop track. Both the transformation parameter and the original edge parameter are
retained literally, with the original chosen-zero equalities explicit.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/SConstruction/ObjectTransformationTrack.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

/-- The exact original weak-natural-transformation cylinder evaluated on an object loop. -/
def objectTransformationTrack (A : C) :
    (W.kZeroObjectLoop (F.obj A)).Homotopy (W.kZeroObjectLoop (G.obj A)) where
  toFun z := weakNaturalTransformationRealizationHomotopy V W hF hG η hη
    (z.1, V.kZeroObjectLoop A z.2)
  continuous_toFun := by fun_prop
  map_zero_left t := by
    rw [ContinuousMap.Homotopy.apply_zero]
    exact congrArg (fun p : Path W.kBasepoint W.kBasepoint => p t)
      (deloopingMap_kZeroObjectLoop hF hF0 A)
  map_one_left t := by
    rw [ContinuousMap.Homotopy.apply_one]
    exact congrArg (fun p : Path W.kBasepoint W.kBasepoint => p t)
      (deloopingMap_kZeroObjectLoop hG hG0 A)
  prop' s t ht := by
    rcases ht with ht | ht
    · subst t
      change weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A 0) = W.kZeroObjectLoop (F.obj A) 0
      simp only [Path.source]
      exact weakNaturalTransformationRealizationHomotopy_fixed_zero
        V W hF hG η hη hF0 hG0 s
    · rw [Set.mem_singleton_iff] at ht
      subst t
      change weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A 1) = W.kZeroObjectLoop (F.obj A) 1
      simp only [Path.target]
      exact weakNaturalTransformationRealizationHomotopy_fixed_zero
        V W hF hG η hη hF0 hG0 s

/-- Both original parameters survive without any choice of a homotopy witness. -/
theorem objectTransformationTrack_apply (A : C) (s t : unitInterval) :
    objectTransformationTrack V W hF hG η hη hF0 hG0 A (s, t) =
      weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A t) := rfl

end CategoryTheory.Waldhausen
