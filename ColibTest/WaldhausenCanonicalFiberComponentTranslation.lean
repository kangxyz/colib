/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberComponentTranslation

/-!
# Coordinate regressions for the prescribed canonical-fiber component translation

These tests use an arbitrary category with independent object and morphism universes.
The first section deliberately has no zero-morphism instance. The suffix and component
section adds only that instance, with no fibration, cylinder or weak-equivalence premise.
Both fiber time and object-loop time are independent throughout. These are source-only
regression statements until native compilation is explicitly resumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open scoped Topology unitInterval

universe u v

namespace ColibTest.WaldhausenCanonicalFiberComponentTranslation

variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (A : C) (X : AcyclicCategory N)

/-- The actual canonical map, not an arbitrary representative of its homotopy class, is looped. -/
theorem original_loop_map :
    canonicalFiberObjectLoop N X =
      basedLoopMap (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        ((acyclicStructure N).kZeroObjectLoop X) := rfl

/-- The original fine source loop retains every loop parameter. -/
theorem original_loop_source (t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.1 = V.kZeroObjectLoop X.obj t :=
  canonicalFiberObjectLoop_projection N X t

/-- The complete stored fiber path uses its independent fiber parameter. -/
theorem original_loop_path (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      acyclicNullhomotopy N (s, (acyclicStructure N).kZeroObjectLoop X t) :=
  canonicalFiberObjectLoop_path N X t s

/-- The full zero-to-inclusion homotopy is reversed in fiber time, not in object-loop time. -/
theorem original_reversed_zero_to_inclusion (s t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      weakNaturalTransformationRealizationHomotopy (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N)
        (unitInterval.symm s, (acyclicStructure N).kZeroObjectLoop X t) := rfl

/-- The transpose uses the inverse of the existing coordinate homeomorphism. -/
theorem original_transpose :
    canonicalFiberObjectLoopTranspose N X =
      (HomotopyFiber.loopFiberHomeomorph (changeWeakMap N) (changeWeakMap_basepoint N)).symm
        (canonicalFiberObjectLoop N X) := rfl

/-- The transpose retains the entire original fine object loop. -/
theorem original_transpose_source :
    (canonicalFiberObjectLoopTranspose N X).val.1 = V.kZeroObjectLoop X.obj :=
  canonicalFiberObjectLoopTranspose_source N X

/-- Transposition swaps the two displayed coordinates without a second reversal. -/
theorem original_transpose_path (s t : unitInterval) :
    (canonicalFiberObjectLoopTranspose N X).val.2 s t =
      (canonicalFiberObjectLoop N X t).val.2 s :=
  canonicalFiberObjectLoopTranspose_path N X s t

/-- The actual reversed nullhomotopy survives the coordinate transpose. -/
theorem original_transpose_nullhomotopy (s t : unitInterval) :
    (canonicalFiberObjectLoopTranspose N X).val.2 s t =
      acyclicNullhomotopy N (s, (acyclicStructure N).kZeroObjectLoop X t) := rfl

/-- Reversal still acts only in fiber time after transposition. -/
theorem original_transpose_reversal (s t : unitInterval) :
    (canonicalFiberObjectLoopTranspose N X).val.2 s t =
      weakNaturalTransformationRealizationHomotopy (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N)
        (unitInterval.symm s, (acyclicStructure N).kZeroObjectLoop X t) := rfl

/-- The stored path starts at the actual image of the original source loop. -/
theorem original_transpose_zero :
    (canonicalFiberObjectLoopTranspose N X).val.2 0 =
      basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
        (V.kZeroObjectLoop X.obj) := by
  rw [(canonicalFiberObjectLoopTranspose N X).property.1,
    canonicalFiberObjectLoopTranspose_source]

/-- The transposed target is the actual constant loop. -/
theorem original_transpose_one :
    (canonicalFiberObjectLoopTranspose N X).val.2 1 = Path.refl N.coarse.kBasepoint :=
  canonicalFiberObjectLoopTranspose_one N X

/-- The strict square uses the actual object-loop naturality theorem and chosen-zero equality. -/
theorem original_localization_object_loop :
    basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N) (V.kZeroObjectLoop A) =
      N.coarse.kZeroObjectLoop A :=
  deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A

/-- Left translation commutes strictly with the unchanged localization loop map. -/
theorem original_prefix_square :
    (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)).toFun.comp
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)) =
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)).comp
        (loopLeftTranslationEquiv (V.kZeroObjectLoop A)).toFun :=
  canonicalFiberPrefix_square N A

/-- Prefix equivalence requires no zero-morphism instance and retains the literal target. -/
example :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (Path.refl N.coarse.kBasepoint))
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))) :=
  canonicalFiberPrefixEquiv N A

/-- On any actual fiber point, the source is literal left concatenation. -/
theorem arbitrary_prefix_source
    (z : HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint)) :
    (canonicalFiberPrefixEquiv N A z).val.1 = (V.kZeroObjectLoop A).trans z.val.1 := by
  change loopLeftTranslationEquiv (V.kZeroObjectLoop A) z.val.1 = _
  exact loopLeftTranslationEquiv_apply _ _

/-- On any actual fiber point, the whole stored path is postcomposed by left translation. -/
theorem arbitrary_prefix_path
    (z : HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint)) :
    (canonicalFiberPrefixEquiv N A z).val.2 =
      (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)).toFun.comp z.val.2 := rfl

/-- The arbitrary-point formula keeps independent fiber and loop parameters. -/
theorem arbitrary_prefix_path_apply
    (z : HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint)) (s t : unitInterval) :
    (canonicalFiberPrefixEquiv N A z).val.2 s t =
      ((N.coarse.kZeroObjectLoop A).trans (z.val.2 s)) t := by
  change loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A) (z.val.2 s) t = _
  rw [loopLeftTranslationEquiv_apply]

/-- The displayed prefixed object retains its literal fine source loop. -/
theorem original_prefixed_source :
    (canonicalFiberObjectPrefixed N A X).val.1 =
      (V.kZeroObjectLoop A).trans (V.kZeroObjectLoop X.obj) :=
  canonicalFiberObjectPrefixed_source N A X

/-- The entire prefixed path is the same specified left translation of the transpose. -/
theorem original_prefixed_path_map :
    (canonicalFiberObjectPrefixed N A X).val.2 =
      (loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)).toFun.comp
        (canonicalFiberObjectLoopTranspose N X).val.2 := rfl

/-- The half-interval formula retains the source's exact interval witnesses. -/
theorem original_prefixed_path (s t : unitInterval) :
    (canonicalFiberObjectPrefixed N A X).val.2 s t =
      if h : (t : ℝ) ≤ 1 / 2 then
        N.coarse.kZeroObjectLoop A
          ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop N X
          ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s :=
  canonicalFiberObjectPrefixed_path N A X s t

/-- The prefix's first half is independent of fiber time. -/
theorem original_prefixed_first_half (s t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    (canonicalFiberObjectPrefixed N A X).val.2 s t =
      N.coarse.kZeroObjectLoop A
        ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩ := by
  rw [canonicalFiberObjectPrefixed_path, dif_pos h]

/-- The prefix's second half retains the full reversed nullhomotopy, at unchanged fiber time. -/
theorem original_prefixed_second_half (s t : unitInterval) (h : ¬ (t : ℝ) ≤ 1 / 2) :
    (canonicalFiberObjectPrefixed N A X).val.2 s t =
      acyclicNullhomotopy N
        (s, (acyclicStructure N).kZeroObjectLoop X
          ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, t.2.2⟩⟩) := by
  rw [canonicalFiberObjectPrefixed_path, dif_neg h, canonicalFiberObjectLoop_path]

/-- The forward equivalence takes the actual transposed loop to the prescribed full point. -/
theorem original_prefix_object :
    canonicalFiberPrefixEquiv N A (canonicalFiberObjectLoopTranspose N X) =
      canonicalFiberObjectPrefixed N A X :=
  canonicalFiberPrefixEquiv_object N A X

section Suffix

variable [HasZeroMorphisms C]

/-- Only zero morphisms are added to form the actual identity-cofiber suffix. -/
example : Path ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))
    (N.coarse.kZeroObjectLoop A) := N.coarse.identityCofiberSuffixPath A

/-- The exact suffix is the actual identity-cofiber triangle, with independent parameters. -/
theorem original_identity_triangle_suffix (s t : unitInterval) :
    N.coarse.identityCofiberSuffixPath A s t =
      N.coarse.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ N.coarse.zero)
        (N.coarse.cof.id_mem A) (QuotientRows.cofiberTwo_identity_square N.coarse) (s, t) :=
  N.coarse.identityCofiberSuffixPath_apply A s t

/-- The prescribed suffix starts at the actual constant-suffixed object loop. -/
theorem original_suffix_zero :
    N.coarse.identityCofiberSuffixPath A 0 =
      (N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint) :=
  (N.coarse.identityCofiberSuffixPath A).source

/-- The prescribed suffix ends at the unchanged object loop. -/
theorem original_suffix_one :
    N.coarse.identityCofiberSuffixPath A 1 = N.coarse.kZeroObjectLoop A :=
  (N.coarse.identityCofiberSuffixPath A).target

/-- The component equivalence targets the actual loop-map fiber, not a component subspace. -/
example :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (Path.refl N.coarse.kBasepoint))
      (HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (N.coarse.kZeroObjectLoop A)) :=
  canonicalFiberComponentEquiv N A

/-- The actual component equivalence is the strict prefix followed by the prescribed transport. -/
theorem original_component_equiv :
    canonicalFiberComponentEquiv N A =
      (canonicalFiberPrefixEquiv N A).trans
        (HomotopyFiber.basepointTransportEquiv
          (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
          (N.coarse.identityCofiberSuffixPath A)) := rfl

/-- The arbitrary-point component map changes its source only by the original left prefix. -/
theorem arbitrary_component_source
    (z : HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint)) :
    (canonicalFiberComponentEquiv N A z).val.1 = (V.kZeroObjectLoop A).trans z.val.1 := by
  change (canonicalFiberPrefixEquiv N A z).val.1 = _
  exact arbitrary_prefix_source N A z

/-- The arbitrary-point component map appends precisely the identity-triangle suffix. -/
theorem arbitrary_component_path
    (z : HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint)) :
    (canonicalFiberComponentEquiv N A z).val.2 =
      ((HomotopyFiber.toPath
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))
        (canonicalFiberPrefixEquiv N A z)).trans
          (N.coarse.identityCofiberSuffixPath A)).toContinuousMap :=
  HomotopyFiber.basepointTransportEquiv_path _ _ _

/-- The particular transported object retains its original fine source loop. -/
theorem original_transport_source :
    (canonicalFiberObjectPrefixTransport N A X).val.1 =
      (V.kZeroObjectLoop A).trans (V.kZeroObjectLoop X.obj) :=
  canonicalFiberObjectPrefixTransport_source N A X

/-- The complete transported path is the entire prescribed prefix followed by the exact suffix. -/
theorem original_transport_path :
    (canonicalFiberObjectPrefixTransport N A X).val.2 =
      ((HomotopyFiber.toPath
        (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))
        (canonicalFiberObjectPrefixed N A X)).trans
          (N.coarse.identityCofiberSuffixPath A)).toContinuousMap :=
  canonicalFiberObjectPrefixTransport_path N A X

/-- Standard path concatenation acts in fiber time while preserving independent loop time. -/
theorem original_transport_path_apply (s t : unitInterval) :
    (canonicalFiberObjectPrefixTransport N A X).val.2 s t =
      if h : (s : ℝ) ≤ 1 / 2 then
        (canonicalFiberObjectPrefixed N A X).val.2
          ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩ t
      else
        N.coarse.identityCofiberSuffixPath A
          ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, s.2.2⟩⟩ t := by
  rw [canonicalFiberObjectPrefixTransport_path]
  change ((HomotopyFiber.toPath
    (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
    ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))
    (canonicalFiberObjectPrefixed N A X)).trans
      (N.coarse.identityCofiberSuffixPath A)) s t = _
  rw [Path.trans_apply]
  split_ifs <;> rfl

/-- The transported first half retains the entire original prefixed path. -/
theorem original_transport_first_half (s t : unitInterval) (h : (s : ℝ) ≤ 1 / 2) :
    (canonicalFiberObjectPrefixTransport N A X).val.2 s t =
      (canonicalFiberObjectPrefixed N A X).val.2
        ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩ t := by
  rw [original_transport_path_apply, dif_pos h]

/-- The full final path retains the reversed zero track inside its prefixed first half. -/
theorem original_transport_reversed_prefix_tail (s t : unitInterval)
    (hs : (s : ℝ) ≤ 1 / 2) (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    (canonicalFiberObjectPrefixTransport N A X).val.2 s t =
      weakNaturalTransformationRealizationHomotopy (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N)
        (unitInterval.symm
          ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩,
          (acyclicStructure N).kZeroObjectLoop X
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) := by
  rw [original_transport_first_half N A X s t hs,
    original_prefixed_second_half N A X _ t ht]
  rfl

/-- The transported second half is the literal cofiber triangle at the rescaled fiber time. -/
theorem original_transport_second_half (s t : unitInterval) (h : ¬ (s : ℝ) ≤ 1 / 2) :
    (canonicalFiberObjectPrefixTransport N A X).val.2 s t =
      N.coarse.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ N.coarse.zero)
        (N.coarse.cof.id_mem A) (QuotientRows.cofiberTwo_identity_square N.coarse)
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  rw [original_transport_path_apply, dif_neg h, Structure.identityCofiberSuffixPath_apply]

/-- The stored final path starts at the localization of the exact prefixed fine loop. -/
theorem original_transport_zero :
    (canonicalFiberObjectPrefixTransport N A X).val.2 0 =
      basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
        ((V.kZeroObjectLoop A).trans (V.kZeroObjectLoop X.obj)) :=
  (canonicalFiberObjectPrefixTransport N A X).property.1

/-- The stored final path ends at the actual target object loop. -/
theorem original_transport_one :
    (canonicalFiberObjectPrefixTransport N A X).val.2 1 = N.coarse.kZeroObjectLoop A :=
  (canonicalFiberObjectPrefixTransport N A X).property.2

/-- The endpoint is an equality of actual fiber points, not merely of homotopy classes. -/
theorem original_component_object :
    canonicalFiberComponentEquiv N A (canonicalFiberObjectLoopTranspose N X) =
      canonicalFiberObjectPrefixTransport N A X :=
  canonicalFiberComponentEquiv_object N A X

/-- The final equivalence value retains the entire translated path at both independent times. -/
theorem original_component_object_path (s t : unitInterval) :
    (canonicalFiberComponentEquiv N A (canonicalFiberObjectLoopTranspose N X)).val.2 s t =
      (canonicalFiberObjectPrefixTransport N A X).val.2 s t := by
  rw [canonicalFiberComponentEquiv_object]

end Suffix

end ColibTest.WaldhausenCanonicalFiberComponentTranslation
