/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.HomotopyPushout
public import Mathlib.Topology.Separation.Basic

/-! # Closed point fibers of the actual reduced double mapping cylinder -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopyPushoutSeparation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original quotient and all endpoint fibers
are retained; only native namespace ownership changes. -/
@[expose] public section

open Topology
noncomputable section
open CategoryTheory Set
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (k : ℕ)

/-- Set-theoretic normal forms compute fibers without changing the original quotient topology. -/
def separationNormalForm : (B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k) →
    Option ((B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k)) := by
  classical
  exact Sum.elim
    (Sum.elim (fun y ↦ if y = B.point k then none else some (.inl (.inl y)))
      (fun y ↦ if y = C.point k then none else some (.inl (.inr y))))
    (fun z ↦ if z.2 = A.point k then none else
      if z.1 = 0 then if f.map k z.2 = B.point k then none else some (.inl (.inl (f.map k z.2)))
      else if z.1 = 1 then if g.map k z.2 = C.point k then none
        else some (.inl (.inr (g.map k z.2)))
      else some (.inr z))

/-- Interpret every representative in the original reduced double cylinder. -/
def separationNormalValue :
    Option ((B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k)) → Space f g k
  | none => point f g k
  | some z => Quot.mk _ z

lemma separationNormalValue_normalForm
    (z : (B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k)) :
    separationNormalValue f g k (separationNormalForm f g k z) = Quot.mk _ z := by
  classical
  cases z with
  | inl y =>
    cases y with
    | inl y =>
      by_cases h : y = B.point k <;>
        simp [separationNormalForm, separationNormalValue, h, point, left]
    | inr y =>
      by_cases h : y = C.point k
      · subst y
        simp only [separationNormalForm, separationNormalValue, Sum.elim_inl, Sum.elim_inr,
          eq_self, ite_true]
        exact (right_point f g k).symm
      · simp [separationNormalForm, separationNormalValue, h]
  | inr z =>
    obtain ⟨s, x⟩ := z
    by_cases hx : x = A.point k
    · subst x
      simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, eq_self, ite_true]
      exact (cylinder_point f g k s).symm
    · by_cases h0 : s = 0
      · subst s
        by_cases hfx : f.map k x = B.point k
        · simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, hx, hfx,
            ite_false, ite_true, eq_self]
          exact (congrArg (left f g k) hfx).symm.trans (cylinder_zero f g k x).symm
        · simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, hx, hfx,
            ite_false, ite_true, eq_self]
          exact (cylinder_zero f g k x).symm
      · by_cases h1 : s = 1
        · subst s
          by_cases hgx : g.map k x = C.point k
          · simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, hx, hgx,
              one_ne_zero, ite_false, ite_true, eq_self]
            exact (right_point f g k).symm.trans
              ((congrArg (right f g k) hgx).symm.trans (cylinder_one f g k x).symm)
          · simp only [separationNormalForm, separationNormalValue, Sum.elim_inr, hx, hgx,
              one_ne_zero, ite_false, ite_true, eq_self]
            exact (cylinder_one f g k x).symm
        · simp [separationNormalForm, separationNormalValue, hx, h0, h1]

lemma separationNormalForm_respects
    {z w : (B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k)}
    (h : Relation f g k z w) : separationNormalForm f g k z = separationNormalForm f g k w := by
  classical
  cases h with
  | left x =>
    by_cases hx : x = A.point k <;> simp [separationNormalForm, hx, f.map_point]
  | right x =>
    by_cases hx : x = A.point k <;> simp [separationNormalForm, hx, g.map_point]
  | base s => simp [separationNormalForm]

lemma quot_eq_iff_separationNormalForm_eq
    (z w : (B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k)) :
    Quot.mk (Relation f g k) z = Quot.mk _ w ↔
      separationNormalForm f g k z = separationNormalForm f g k w := by
  constructor
  · exact congrArg (Quot.lift (separationNormalForm f g k)
      (fun _ _ ↦ separationNormalForm_respects f g k))
  · intro h
    simpa only [separationNormalValue_normalForm] using
      congrArg (separationNormalValue f g k) h

/-- The common base fiber contains both full endpoint preimages and the source base line. -/
lemma separationNormalForm_cylinder_none (z : unitInterval × A.space k) :
    separationNormalForm f g k (.inr z) = none ↔
      z.2 = A.point k ∨ z.1 = 0 ∧ f.map k z.2 = B.point k ∨
        z.1 = 1 ∧ g.map k z.2 = C.point k := by
  classical
  by_cases hx : z.2 = A.point k
  · simp [separationNormalForm, hx]
  · by_cases h0 : z.1 = 0
    · simp [separationNormalForm, hx, h0]
    · by_cases h1 : z.1 = 1 <;> simp [separationNormalForm, hx, h0, h1]

lemma separationNormalForm_some_valid
    {z w : (B.space k ⊕ C.space k) ⊕ (unitInterval × A.space k)}
    (h : separationNormalForm f g k z = some w) :
    match w with
    | .inl (.inl y) => y ≠ B.point k
    | .inl (.inr y) => y ≠ C.point k
    | .inr v => v.2 ≠ A.point k ∧ v.1 ≠ 0 ∧ v.1 ≠ 1 := by
  classical
  cases z with
  | inl y =>
    cases y with
    | inl y =>
      simp only [separationNormalForm, Sum.elim_inl] at h
      split_ifs at h with hy
      cases Option.some.inj h
      exact hy
    | inr y =>
      simp only [separationNormalForm, Sum.elim_inl, Sum.elim_inr] at h
      split_ifs at h with hy
      cases Option.some.inj h
      exact hy
  | inr v =>
    simp only [separationNormalForm, Sum.elim_inr] at h
    split_ifs at h with hx h0 hf h1 hg
    · cases Option.some.inj h
      exact hf
    · cases Option.some.inj h
      exact hg
    · cases Option.some.inj h
      exact ⟨hx, h0, h1⟩

lemma separationNormalForm_cylinder_left (z : unitInterval × A.space k)
    (y : B.space k) (hy : y ≠ B.point k) :
    separationNormalForm f g k (.inr z) = some (.inl (.inl y)) ↔
      z.1 = 0 ∧ f.map k z.2 = y := by
  classical
  by_cases hx : z.2 = A.point k
  · simp [separationNormalForm, hx, f.map_point, Ne.symm hy]
  · by_cases h0 : z.1 = 0
    · by_cases hf : f.map k z.2 = B.point k <;>
        simp [separationNormalForm, hx, h0, hf, Ne.symm hy]
    · by_cases h1 : z.1 = 1 <;> simp [separationNormalForm, hx, h0, h1]

lemma separationNormalForm_cylinder_right (z : unitInterval × A.space k)
    (y : C.space k) (hy : y ≠ C.point k) :
    separationNormalForm f g k (.inr z) = some (.inl (.inr y)) ↔
      z.1 = 1 ∧ g.map k z.2 = y := by
  classical
  by_cases hx : z.2 = A.point k
  · simp [separationNormalForm, hx, g.map_point, Ne.symm hy]
  · by_cases h0 : z.1 = 0
    · simp [separationNormalForm, hx, h0]
    · by_cases h1 : z.1 = 1
      · by_cases hg : g.map k z.2 = C.point k <;>
          simp [separationNormalForm, hx, h1, hg, Ne.symm hy]
      · simp [separationNormalForm, hx, h0, h1]

lemma separationNormalForm_cylinder_interior (z w : unitInterval × A.space k)
    (hw : w.2 ≠ A.point k ∧ w.1 ≠ 0 ∧ w.1 ≠ 1) :
    separationNormalForm f g k (.inr z) = some (.inr w) ↔ z = w := by
  classical
  constructor
  · simp only [separationNormalForm, Sum.elim_inr]
    split_ifs <;> simp
  · rintro rfl
    simp [separationNormalForm, hw.1, hw.2.1, hw.2.2]

/-- The literal common basepoint fiber includes both full endpoint preimages. -/
lemma cylinder_eq_point_iff (z : unitInterval × A.space k) :
    cylinder f g k z = point f g k ↔
      z.2 = A.point k ∨ z.1 = 0 ∧ f.map k z.2 = B.point k ∨
        z.1 = 1 ∧ g.map k z.2 = C.point k := by
  change Quot.mk (Relation f g k) (.inr z) = Quot.mk _ (.inl (.inl (B.point k))) ↔ _
  rw [quot_eq_iff_separationNormalForm_eq f g k]
  simpa only [separationNormalForm, Sum.elim_inl, ite_true, eq_self] using
    separationNormalForm_cylinder_none f g k z

/-- Nonbase left fibers retain every point sent there by the original left map. -/
lemma cylinder_eq_left_iff (z : unitInterval × A.space k)
    (y : B.space k) (hy : y ≠ B.point k) :
    cylinder f g k z = left f g k y ↔ z.1 = 0 ∧ f.map k z.2 = y := by
  change Quot.mk (Relation f g k) (.inr z) = Quot.mk _ (.inl (.inl y)) ↔ _
  rw [quot_eq_iff_separationNormalForm_eq f g k]
  simpa only [separationNormalForm, Sum.elim_inl, ite_eq_right hy] using
    separationNormalForm_cylinder_left f g k z y hy

/-- Nonbase right fibers retain every point sent there by the original right map. -/
lemma cylinder_eq_right_iff (z : unitInterval × A.space k)
    (y : C.space k) (hy : y ≠ C.point k) :
    cylinder f g k z = right f g k y ↔ z.1 = 1 ∧ g.map k z.2 = y := by
  change Quot.mk (Relation f g k) (.inr z) = Quot.mk _ (.inl (.inr y)) ↔ _
  rw [quot_eq_iff_separationNormalForm_eq f g k]
  simpa only [separationNormalForm, Sum.elim_inl, Sum.elim_inr, ite_eq_right hy] using
    separationNormalForm_cylinder_right f g k z y hy

variable [T1Space (A.space k)] [T1Space (B.space k)] [T1Space (C.space k)]

omit [T1Space (A.space k)] in
/-- Both original target summands have closed point fibers. -/
lemma isClosed_target_fiber (q : Space f g k) :
    IsClosed ((fun y : B.space k ⊕ C.space k ↦ Quot.mk (Relation f g k) (.inl y)) ⁻¹' {q}) := by
  classical
  induction q using Quot.inductionOn with
  | h w =>
    have he : (fun y : B.space k ⊕ C.space k ↦ Quot.mk (Relation f g k) (.inl y)) ⁻¹'
        {Quot.mk (Relation f g k) w} =
        {y | separationNormalForm f g k (.inl y) = separationNormalForm f g k w} := by
      ext y
      exact quot_eq_iff_separationNormalForm_eq f g k _ _
    rw [he]
    apply isClosed_sum_iff.mpr
    cases hv : separationNormalForm f g k w with
    | none => simp [separationNormalForm]
    | some v =>
      have hv' := separationNormalForm_some_valid f g k hv
      cases v with
      | inl y =>
        cases y with
        | inl y =>
          have hleft : {z : B.space k | separationNormalForm f g k (.inl (.inl z)) =
              some (.inl (.inl y))} = {y} := by
            ext z
            by_cases hz : z = B.point k <;> simp [separationNormalForm, hz, Ne.symm hv']
          simpa only [preimage_ofPred_eq, hleft] using
            (show IsClosed ({y} : Set (B.space k)) ∧
              IsClosed {z : C.space k | separationNormalForm f g k (.inl (.inr z)) =
                some (.inl (.inl y))} from ⟨isClosed_singleton, by simp [separationNormalForm]⟩)
        | inr y =>
          have hright : {z : C.space k | separationNormalForm f g k (.inl (.inr z)) =
              some (.inl (.inr y))} = {y} := by
            ext z
            by_cases hz : z = C.point k <;> simp [separationNormalForm, hz, Ne.symm hv']
          simpa only [preimage_ofPred_eq, hright] using
            (show IsClosed {z : B.space k | separationNormalForm f g k (.inl (.inl z)) =
                some (.inl (.inr y))} ∧ IsClosed ({y} : Set (C.space k)) from
              ⟨by simp [separationNormalForm], isClosed_singleton⟩)
      | inr z => simp [separationNormalForm]

/-- Original cylinder fibers are closed even when either endpoint map is noninjective. -/
lemma isClosed_cylinder_fiber (q : Space f g k) :
    IsClosed ((cylinder f g k) ⁻¹' {q}) := by
  classical
  induction q using Quot.inductionOn with
  | h w =>
    have he : (cylinder f g k) ⁻¹' {Quot.mk (Relation f g k) w} =
        {z | separationNormalForm f g k (.inr z) = separationNormalForm f g k w} := by
      ext z
      exact quot_eq_iff_separationNormalForm_eq f g k _ _
    rw [he]
    cases hv : separationNormalForm f g k w with
    | none =>
      simp_rw [separationNormalForm_cylinder_none]
      exact (isClosed_singleton.preimage continuous_snd).union
        (((isClosed_singleton.preimage continuous_fst).inter
          (isClosed_singleton.preimage ((f.map k).continuous.comp continuous_snd))).union
          ((isClosed_singleton.preimage continuous_fst).inter
            (isClosed_singleton.preimage ((g.map k).continuous.comp continuous_snd))))
    | some v =>
      have hv' := separationNormalForm_some_valid f g k hv
      cases v with
      | inl y =>
        cases y with
        | inl y =>
          simp_rw [separationNormalForm_cylinder_left f g k _ y hv']
          exact (isClosed_singleton.preimage continuous_fst).inter
            (isClosed_singleton.preimage ((f.map k).continuous.comp continuous_snd))
        | inr y =>
          simp_rw [separationNormalForm_cylinder_right f g k _ y hv']
          exact (isClosed_singleton.preimage continuous_fst).inter
            (isClosed_singleton.preimage ((g.map k).continuous.comp continuous_snd))
      | inr z =>
        simp_rw [separationNormalForm_cylinder_interior f g k _ z hv']
        exact isClosed_singleton

/-- T1 input stages give the unchanged reduced double mapping cylinder a T1 topology. -/
instance spaceT1Space : T1Space (Space f g k) where
  t1 q := by
    apply isQuotientMap_quot_mk.isClosed_preimage.mp
    apply isClosed_sum_iff.mpr
    exact ⟨isClosed_target_fiber f g k q, isClosed_cylinder_fiber f g k q⟩

/-- The actual prespectrum level carries the quotient separation instance. -/
instance prespectrumSpaceT1Space : T1Space ((prespectrum f g).space k) := spaceT1Space f g k

end Topology.LoopPrespectrum.HomotopyPushout
