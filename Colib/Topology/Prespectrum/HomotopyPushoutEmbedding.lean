/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.HomotopyPushoutSeparation

/-!
# The original left inclusion is a closed embedding

The original reduced double-cylinder normal forms show that the left endpoint inclusion is
injective. Its arbitrary closed-subset images have closed preimages on both target summands
and on the full cylinder. Thus T1 original corners give a closed embedding, without any
injectivity assumption on either attaching arrow or any additional cofibration hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Set
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (k : ℕ)

/-- The original reduced-cylinder quotient does not identify distinct left endpoint points. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/HomotopyPushoutEmbedding.lean:29"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem left_injective : Function.Injective (left f g k) := by
  intro x y h
  have hn := (quot_eq_iff_separationNormalForm_eq f g k
    (.inl (.inl x)) (.inl (.inl y))).mp h
  by_cases hx : x = B.point k <;> by_cases hy : y = B.point k
  · exact hx.trans hy.symm
  · simp [separationNormalForm, hx, hy] at hn
  · simp [separationNormalForm, hx, hy] at hn
  · simpa [separationNormalForm, hx, hy] using hn

/-- The two original endpoint images meet exactly at their common basepoint. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/HomotopyPushoutEmbedding.lean:40"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem right_mem_left_image_iff (S : Set (B.space k)) (z : C.space k) :
    right f g k z ∈ left f g k '' S ↔ B.point k ∈ S ∧ z = C.point k := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hn := (quot_eq_iff_separationNormalForm_eq f g k
      (.inl (.inl y)) (.inl (.inr z))).mp he
    by_cases hY : y = B.point k <;> by_cases hZ : z = C.point k
    · exact ⟨hY ▸ hy, hZ⟩
    · simp [separationNormalForm, hY, hZ] at hn
    · simp [separationNormalForm, hY, hZ] at hn
    · simp [separationNormalForm, hY, hZ] at hn
  · rintro ⟨hS, rfl⟩
    exact ⟨B.point k, hS, (right_point f g k).symm⟩

/-- A cylinder point reaches a left subset only through the original zero face or base fiber. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/HomotopyPushoutEmbedding.lean:55"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem cylinder_mem_left_image_iff (S : Set (B.space k)) (z : unitInterval × A.space k) :
    cylinder f g k z ∈ left f g k '' S ↔
      (B.point k ∈ S ∧ cylinder f g k z = point f g k) ∨
        z.1 = 0 ∧ f.map k z.2 ∈ S := by
  constructor
  · rintro ⟨y, hy, he⟩
    by_cases hyp : y = B.point k
    · subst y
      exact Or.inl ⟨hy, he.symm⟩
    · obtain ⟨hs, hf⟩ := (cylinder_eq_left_iff f g k z y hyp).mp he.symm
      exact Or.inr ⟨hs, hf ▸ hy⟩
  · rintro (⟨hS, he⟩ | ⟨hs, hf⟩)
    · exact ⟨B.point k, hS, he.symm⟩
    · exact ⟨f.map k z.2, hf,
        (cylinder_zero f g k z.2).symm.trans (congrArg (cylinder f g k) (Prod.ext hs.symm rfl))⟩

variable [T1Space (A.space k)] [T1Space (B.space k)] [T1Space (C.space k)]

/-- Every closed subset of the original left target has closed image in the reduced quotient. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/HomotopyPushoutEmbedding.lean:74"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem isClosedMap_left : IsClosedMap (left f g k) := by
  intro S hS
  apply isQuotientMap_quot_mk.isClosed_preimage.mp
  apply isClosed_sum_iff.mpr
  constructor
  · apply isClosed_sum_iff.mpr
    constructor
    · change IsClosed ((left f g k) ⁻¹' ((left f g k) '' S))
      simpa only [Set.preimage_image_eq _ (left_injective f g k)] using hS
    · change IsClosed {z : C.space k | right f g k z ∈ left f g k '' S}
      simp_rw [right_mem_left_image_iff]
      exact isClosed_const.inter isClosed_singleton
  · change IsClosed {z : unitInterval × A.space k | cylinder f g k z ∈ left f g k '' S}
    simp_rw [cylinder_mem_left_image_iff]
    exact (isClosed_const.inter (isClosed_singleton.preimage (cylinder f g k).continuous)).union
      ((isClosed_singleton.preimage continuous_fst).inter
        (hS.preimage ((f.map k).continuous.comp continuous_snd)))

/-- The actual left endpoint inclusion of the original reduced pushout is a closed embedding. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/HomotopyPushoutEmbedding.lean:93"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem isClosedEmbedding_inl : IsClosedEmbedding ((inl f g).map k) :=
  .of_continuous_injective_isClosedMap (left f g k).continuous
    (left_injective f g k) (isClosedMap_left f g k)

end Topology.LoopPrespectrum.HomotopyPushout
