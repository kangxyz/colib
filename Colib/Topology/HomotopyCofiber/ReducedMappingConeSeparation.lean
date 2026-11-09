/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.ReducedMappingCone
public import Mathlib.Topology.Separation.Basic

/-! # Closed point fibers of the actual reduced mapping cone -/
/-! Implementation provenance:
`Quillen/Topology/HomotopyCofiber/ReducedMappingConeSeparation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original quotient and all endpoint fibers
are retained; only native namespace ownership changes. -/
@[expose] public section

open Topology
noncomputable section
open Set
open scoped unitInterval
universe u v
namespace Topology.ReducedMappingCone
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)

/-- Set-theoretic representatives used solely to compute the original quotient fibers. -/
def separationNormalForm : Y ⊕ (unitInterval × X) → Option (Y ⊕ (unitInterval × X)) := by
  classical
  exact Sum.elim (fun y ↦ if y = y₀ then none else some (.inl y))
    (fun z ↦ if z.2 = x₀ ∨ z.1 = 1 then none else
      if z.1 = 0 then if f z.2 = y₀ then none else some (.inl (f z.2))
      else some (.inr z))

/-- Interpret representatives in the unchanged mapping-cone quotient. -/
def separationNormalValue : Option (Y ⊕ (unitInterval × X)) → Space x₀ y₀ f
  | none => point x₀ y₀ f
  | some z => Quot.mk _ z

lemma separationNormalValue_normalForm (z : Y ⊕ (unitInterval × X)) :
    separationNormalValue x₀ y₀ f (separationNormalForm x₀ y₀ f z) = Quot.mk _ z := by
  classical
  cases z with
  | inl y =>
    by_cases h : y = y₀ <;> simp [separationNormalForm, separationNormalValue, h, point, inr]
  | inr z =>
    obtain ⟨s, x⟩ := z
    by_cases hx : x = x₀
    · subst x
      simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, true_or,
        ite_true, eq_self]
      exact (cylinder_base x₀ y₀ f s).symm
    · by_cases hs : s = 1
      · subst s
        simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, or_true,
          ite_true, eq_self]
        exact (cylinder_one x₀ y₀ f x).symm
      · by_cases h0 : s = 0
        · subst s
          by_cases hfx : f x = y₀
          · simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, hx, hfx,
              zero_ne_one, false_or, ite_false, ite_true, eq_self]
            exact (congrArg (inr x₀ y₀ f) hfx).symm.trans (cylinder_zero x₀ y₀ f x).symm
          · simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, hx, hfx,
              zero_ne_one, false_or, ite_false, ite_true, eq_self]
            exact (cylinder_zero x₀ y₀ f x).symm
        · simp [separationNormalForm, separationNormalValue, hx, hs, h0]

include hf in
lemma separationNormalForm_respects {z w : Y ⊕ (unitInterval × X)}
    (h : Relation x₀ y₀ f z w) :
    separationNormalForm x₀ y₀ f z = separationNormalForm x₀ y₀ f w := by
  classical
  cases h with
  | bottom x =>
    by_cases hx : x = x₀ <;> simp [separationNormalForm, hx, hf]
  | top x => simp [separationNormalForm]
  | base s => simp [separationNormalForm]

include hf in
lemma quot_eq_iff_separationNormalForm_eq (z w : Y ⊕ (unitInterval × X)) :
    Quot.mk (Relation x₀ y₀ f) z = Quot.mk _ w ↔
      separationNormalForm x₀ y₀ f z = separationNormalForm x₀ y₀ f w := by
  constructor
  · exact congrArg (Quot.lift (separationNormalForm x₀ y₀ f)
      (fun _ _ ↦ separationNormalForm_respects x₀ y₀ f hf))
  · intro h
    simpa only [separationNormalValue_normalForm] using
      congrArg (separationNormalValue x₀ y₀ f) h

/-- The collapsed cylinder fiber includes the entire bottom fiber over the target basepoint. -/
lemma separationNormalForm_cylinder_none (z : unitInterval × X) :
    separationNormalForm x₀ y₀ f (.inr z) = none ↔
      z.2 = x₀ ∨ z.1 = 1 ∨ z.1 = 0 ∧ f z.2 = y₀ := by
  classical
  by_cases hx : z.2 = x₀ <;> by_cases h1 : z.1 = 1 <;>
    by_cases h0 : z.1 = 0 <;> simp [separationNormalForm, hx, h1, h0]

/-- A noncollapsed representative is either a nonbase target or a strict cylinder interior. -/
lemma separationNormalForm_some_valid {z w : Y ⊕ (unitInterval × X)}
    (h : separationNormalForm x₀ y₀ f z = some w) :
    match w with
    | .inl y => y ≠ y₀
    | .inr v => v.2 ≠ x₀ ∧ v.1 ≠ 0 ∧ v.1 ≠ 1 := by
  classical
  cases z with
  | inl y =>
    simp only [separationNormalForm, Sum.elim_inl] at h
    split_ifs at h with hy
    cases Option.some.inj h
    exact hy
  | inr v =>
    simp only [separationNormalForm, Sum.elim_inr] at h
    split_ifs at h with hb h0 hy
    · cases Option.some.inj h
      exact hy
    · cases Option.some.inj h
      exact ⟨(not_or.mp hb).1, h0, (not_or.mp hb).2⟩

include hf in
lemma separationNormalForm_cylinder_target (z : unitInterval × X) (y : Y) (hy : y ≠ y₀) :
    separationNormalForm x₀ y₀ f (.inr z) = some (.inl y) ↔ z.1 = 0 ∧ f z.2 = y := by
  classical
  by_cases hx : z.2 = x₀
  · simp [separationNormalForm, hx, hf, Ne.symm hy]
  · by_cases h1 : z.1 = 1
    · simp [separationNormalForm, hx, h1]
    · by_cases h0 : z.1 = 0
      · by_cases hfx : f z.2 = y₀
        · simp [separationNormalForm, hx, h0, hfx, Ne.symm hy]
        · simp [separationNormalForm, hx, h0, hfx]
      · simp [separationNormalForm, hx, h1, h0]

lemma separationNormalForm_cylinder_interior (z w : unitInterval × X)
    (hw : w.2 ≠ x₀ ∧ w.1 ≠ 0 ∧ w.1 ≠ 1) :
    separationNormalForm x₀ y₀ f (.inr z) = some (.inr w) ↔ z = w := by
  classical
  constructor
  · simp only [separationNormalForm, Sum.elim_inr]
    split_ifs <;> simp
  · rintro rfl
    simp [separationNormalForm, hw.1, hw.2.1, hw.2.2]

include hf in
/-- The literal basepoint fiber of the original cone cylinder. -/
lemma cylinder_eq_point_iff (z : unitInterval × X) :
    cylinder x₀ y₀ f z = point x₀ y₀ f ↔
      z.2 = x₀ ∨ z.1 = 1 ∨ z.1 = 0 ∧ f z.2 = y₀ := by
  change Quot.mk (Relation x₀ y₀ f) (.inr z) = Quot.mk _ (.inl y₀) ↔ _
  rw [quot_eq_iff_separationNormalForm_eq x₀ y₀ f hf]
  simpa only [separationNormalForm, Sum.elim_inl, ite_true, eq_self] using
    separationNormalForm_cylinder_none x₀ y₀ f z

include hf in
/-- Every nonbase target fiber keeps all original points sent there, without injectivity. -/
lemma cylinder_eq_inr_iff (z : unitInterval × X) (y : Y) (hy : y ≠ y₀) :
    cylinder x₀ y₀ f z = inr x₀ y₀ f y ↔ z.1 = 0 ∧ f z.2 = y := by
  change Quot.mk (Relation x₀ y₀ f) (.inr z) = Quot.mk _ (.inl y) ↔ _
  rw [quot_eq_iff_separationNormalForm_eq x₀ y₀ f hf]
  simpa only [separationNormalForm, Sum.elim_inl, ite_eq_right hy] using
    separationNormalForm_cylinder_target x₀ y₀ f hf z y hy

variable [T1Space X] [T1Space Y]

omit [T1Space X] in
include hf in
/-- The original target inclusion has closed point fibers. -/
lemma isClosed_inr_fiber (q : Space x₀ y₀ f) : IsClosed ((inr x₀ y₀ f) ⁻¹' {q}) := by
  classical
  induction q using Quot.inductionOn with
  | h w =>
    have he : (inr x₀ y₀ f) ⁻¹' {Quot.mk (Relation x₀ y₀ f) w} =
        {y | separationNormalForm x₀ y₀ f (.inl y) = separationNormalForm x₀ y₀ f w} := by
      ext y
      exact quot_eq_iff_separationNormalForm_eq x₀ y₀ f hf _ _
    rw [he]
    cases hv : separationNormalForm x₀ y₀ f w with
    | none => simp [separationNormalForm]
    | some v =>
      have hv' := separationNormalForm_some_valid x₀ y₀ f hv
      cases v with
      | inl y =>
        have he : {z : Y | separationNormalForm x₀ y₀ f (.inl z) = some (.inl y)} = {y} := by
          ext z
          by_cases hz : z = y₀ <;> simp [separationNormalForm, hz, Ne.symm hv']
        rw [he]
        exact isClosed_singleton
      | inr z => simp [separationNormalForm]

include hf in
/-- The original cylinder has closed point fibers, including every endpoint preimage. -/
lemma isClosed_cylinder_fiber (q : Space x₀ y₀ f) :
    IsClosed ((cylinder x₀ y₀ f) ⁻¹' {q}) := by
  classical
  induction q using Quot.inductionOn with
  | h w =>
    have he : (cylinder x₀ y₀ f) ⁻¹' {Quot.mk (Relation x₀ y₀ f) w} =
        {z | separationNormalForm x₀ y₀ f (.inr z) = separationNormalForm x₀ y₀ f w} := by
      ext z
      exact quot_eq_iff_separationNormalForm_eq x₀ y₀ f hf _ _
    rw [he]
    cases hv : separationNormalForm x₀ y₀ f w with
    | none =>
      simp_rw [separationNormalForm_cylinder_none]
      exact (isClosed_singleton.preimage continuous_snd).union
        ((isClosed_singleton.preimage continuous_fst).union
          ((isClosed_singleton.preimage continuous_fst).inter
            (isClosed_singleton.preimage (f.continuous.comp continuous_snd))))
    | some v =>
      have hv' := separationNormalForm_some_valid x₀ y₀ f hv
      cases v with
      | inl y =>
        simp_rw [separationNormalForm_cylinder_target x₀ y₀ f hf _ y hv']
        exact (isClosed_singleton.preimage continuous_fst).inter
          (isClosed_singleton.preimage (f.continuous.comp continuous_snd))
      | inr z =>
        simp_rw [separationNormalForm_cylinder_interior x₀ y₀ f _ z hv']
        exact isClosed_singleton

include hf in
/-- The actual reduced mapping cone of a based map between T1 spaces is T1. -/
theorem space_t1Space : T1Space (Space x₀ y₀ f) where
  t1 q := by
    apply isQuotientMap_quot_mk.isClosed_preimage.mp
    apply isClosed_sum_iff.mpr
    exact ⟨isClosed_inr_fiber x₀ y₀ f hf q, isClosed_cylinder_fiber x₀ y₀ f hf q⟩

end Topology.ReducedMappingCone
