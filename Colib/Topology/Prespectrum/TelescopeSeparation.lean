/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Telescope
public import Mathlib.Topology.Separation.Basic

/-!
# Separation of the original reduced telescope

For T1 stage spaces, the original reduced telescope is T1. Normal forms are
used only to compute fibers of the original quotient: the base ray and all
upper endpoints sent to a basepoint form one fiber. Nonbase endpoint fibers
include the original incoming mapping fibers. The topology and telescope maps
are unchanged.
-/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Set
open scoped unitInterval
open unitInterval
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)

/-- A set-theoretic normal form for computing original quotient fibers. -/
def normalForm (z : Σ i, I × (E i).space k) : Option (Σ i, I × (E i).space k) := by
  classical
  exact if z.2.1 = 1 then
    if (f z.1).map k z.2.2 = (E (z.1 + 1)).point k then none
    else some ⟨z.1 + 1, (0, (f z.1).map k z.2.2)⟩
  else if z.2.2 = (E z.1).point k then none else some z

/-- Interpret a normal form in the original reduced quotient. -/
def normalFormValue : Option (Σ i, I × (E i).space k) → Space E f k
  | none => point E f k
  | some z => cylinder E f k z.1 z.2

@[simp] theorem normalFormValue_normalForm (z : Σ i, I × (E i).space k) :
    normalFormValue E f k (normalForm E f k z) = Quot.mk _ z := by
  classical
  obtain ⟨i, s, x⟩ := z
  simp only [normalForm]
  split_ifs with hs hx hx
  · subst s
    change point E f k = cylinder E f k i (1, x)
    rw [cylinder_one, hx, cylinder_point]
  · subst s
    exact (cylinder_one E f k i x).symm
  · subst x
    exact (cylinder_point E f k i s).symm
  · rfl

/-- The normal form respects both generating identifications. -/
theorem normalForm_respects {z w : Σ i, I × (E i).space k}
    (h : Relation E f k z w) : normalForm E f k z = normalForm E f k w := by
  classical
  cases h with
  | step i x => simp [normalForm]
  | base i s => simp [normalForm, (f i).map_point]

/-- Equality in the original quotient is detected by normal forms. -/
theorem quot_eq_iff_normalForm_eq (z w : Σ i, I × (E i).space k) :
    Quot.mk (Relation E f k) z = Quot.mk _ w ↔ normalForm E f k z = normalForm E f k w := by
  classical
  constructor
  · exact congrArg (Quot.lift (normalForm E f k) (fun _ _ ↦ normalForm_respects E f k))
  · intro h
    simpa only [normalFormValue_normalForm] using congrArg (normalFormValue E f k) h

/-- A nonbase normal form never lies at an upper endpoint or at a stage basepoint. -/
theorem normalForm_some_valid {z w : Σ i, I × (E i).space k}
    (h : normalForm E f k z = some w) : w.2.1 ≠ 1 ∧ w.2.2 ≠ (E w.1).point k := by
  classical
  obtain ⟨i, s, x⟩ := z
  simp only [normalForm] at h
  split_ifs at h with hs hx hx
  · cases Option.some.inj h
    exact ⟨zero_ne_one, hx⟩
  · cases Option.some.inj h
    exact ⟨hs, hx⟩

/-- The collapsed fiber includes exactly the base line and the incoming upper fiber. -/
theorem normalForm_eq_none_iff (i : ℕ) (z : I × (E i).space k) :
    normalForm E f k ⟨i, z⟩ = none ↔
      z.2 = (E i).point k ∨ z.1 = 1 ∧ (f i).map k z.2 = (E (i + 1)).point k := by
  classical
  by_cases hx : z.2 = (E i).point k
  · simp [normalForm, hx, (f i).map_point]
  · by_cases hs : z.1 = 1 <;> simp [normalForm, hx, hs]

/-- A nonbase fiber is a single lower slice together with its incoming upper slice. -/
theorem normalForm_eq_some_iff (i : ℕ) (z : I × (E i).space k)
    (w : Σ j, I × (E j).space k) (hw : w.2.1 ≠ 1 ∧ w.2.2 ≠ (E w.1).point k) :
    normalForm E f k ⟨i, z⟩ = some w ↔
      (⟨i, z⟩ : Σ j, I × (E j).space k) = w ∨
        z.1 = 1 ∧ (⟨i + 1, (0, (f i).map k z.2)⟩ : Σ j, I × (E j).space k) = w := by
  classical
  constructor
  · intro h
    simp only [normalForm] at h
    split_ifs at h with hs hx hx
    · exact Or.inr ⟨hs, Option.some.inj h⟩
    · exact Or.inl (Option.some.inj h)
  · rintro (h | ⟨hs, h⟩)
    · subst w
      simp [normalForm, hw.1, hw.2]
    · subst w
      simp [normalForm, hs, hw.2]

variable [∀ i, T1Space ((E i).space k)]

/-- Every original cylinder has closed point fibers in the reduced quotient. -/
theorem isClosed_cylinder_fiber (i : ℕ) (q : Space E f k) :
    IsClosed ((cylinder E f k i) ⁻¹' {q}) := by
  induction q using Quot.inductionOn with
  | h w =>
    have heq : (cylinder E f k i) ⁻¹' {Quot.mk (Relation E f k) w} =
        {z | normalForm E f k ⟨i, z⟩ = normalForm E f k w} := by
      ext z
      exact quot_eq_iff_normalForm_eq E f k ⟨i, z⟩ w
    rw [heq]
    cases hv : normalForm E f k w with
    | none =>
      simp_rw [normalForm_eq_none_iff]
      exact (isClosed_singleton.preimage continuous_snd).union
        ((isClosed_singleton.preimage continuous_fst).inter
          (isClosed_singleton.preimage (((f i).map k).continuous.comp continuous_snd)))
    | some v =>
      simp_rw [normalForm_eq_some_iff E f k i _ v (normalForm_some_valid E f k hv)]
      have hvclosed : IsClosed ({v} : Set (Σ j, I × (E j).space k)) := by
        obtain ⟨j, v⟩ := v
        simpa only [image_singleton] using
          (@isClosedMap_sigmaMk ℕ (fun n ↦ I × (E n).space k)
            (fun _ ↦ inferInstance) j {v} isClosed_singleton)
      have hstart : IsClosed {z : I × (E i).space k |
          (⟨i, z⟩ : Σ j, I × (E j).space k) = v} :=
        hvclosed.preimage (continuous_sigmaMk (i := i))
      have hfinish : IsClosed {z : I × (E i).space k |
          (⟨i + 1, (0, (f i).map k z.2)⟩ : Σ j, I × (E j).space k) = v} :=
        hvclosed.preimage ((continuous_sigmaMk (i := i + 1)).comp
          (continuous_const.prodMk (((f i).map k).continuous.comp continuous_snd)))
      exact hstart.union ((isClosed_singleton.preimage continuous_fst).inter hfinish)

/-- T1 stages give the original reduced quotient a T1 topology. -/
instance spaceT1Space : T1Space (Space E f k) where
  t1 q := by
    apply isQuotientMap_quot_mk.isClosed_preimage.mp
    apply isClosed_sigma_iff.mpr
    intro i
    exact isClosed_cylinder_fiber E f k i q

end Topology.LoopPrespectrum.Telescope
