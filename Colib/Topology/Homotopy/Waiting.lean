/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.NormNum

/-!
# Waiting homotopies with exactly compatible extension times

A `WaitingHomotopy f g b` is a homotopy which agrees with its initial map
through time `b`. Given actual maps `j : A → B`, `r : B → A`, an actual
homotopy `R` from the identity of `B` to `j ∘ r`, and an extension `f` of the
old initial map, `WaitingHomotopy.extendWaiting` first applies `f` to the
radial homotopy and then applies the old homotopy at its unchanged time.
The radial phase uses a clipped affine ramp from a new waiting time `a` to
the old waiting time `b`. Continuity follows by closed pasting at `b`.

If `r ∘ j = id` and the radial homotopy fixes `j(A)` at every time, the new
homotopy restricts to the old homotopy at exactly the same time, including
the seam. No reparametrization of the old homotopy is used. The hypotheses
allow `b = 1`; the proof at the terminal endpoint includes that case.

`dyadicWait` and `WaitingHomotopy.extendDyadic` supply strictly decreasing
positive waiting times for an inductive construction. These constructions
accept the actual radial homotopy and extension map; they do not assert
that such geometric data exist for a particular cell attachment.

Adapted from `Quillen/Topology/Homotopy/Waiting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace Topology

universe u v w

variable {A : Type u} {B : Type v} {X : Type w}
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

/-- A homotopy which remains at its initial map through a specified real time.
The time is real so that waiting bounds can be compared without subtype casts. -/
structure WaitingHomotopy (f g : C(A, X)) (wait : ℝ) where
  /-- The actual continuous homotopy. -/
  toHomotopy : ContinuousMap.Homotopy f g
  /-- The entire closed initial time interval is stationary. -/
  stationary : ∀ (t : I) (z : A), (t : ℝ) ≤ wait → toHomotopy (t, z) = f z

/-- The affine ramp from `start` to `finish`, clipped to the unit interval. -/
def waitingRamp (start finish : ℝ) : C(I, I) where
  toFun t := Set.projIcc 0 1 zero_le_one (((t : ℝ) - start) / (finish - start))
  continuous_toFun := continuous_projIcc.comp
    ((continuous_subtype_val.sub continuous_const).div_const (finish - start))

/-- The clipped ramp vanishes on the entire initial waiting interval. -/
theorem waitingRamp_eq_zero {start finish : ℝ} (hlt : start < finish)
    {t : I} (ht : (t : ℝ) ≤ start) : waitingRamp start finish t = 0 := by
  exact Set.projIcc_of_le_left zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlt.le))

/-- The clipped ramp has reached one at and after the old waiting time. -/
theorem waitingRamp_eq_one {start finish : ℝ} (hlt : start < finish)
    {t : I} (ht : finish ≤ (t : ℝ)) : waitingRamp start finish t = 1 := by
  exact Set.projIcc_of_right_le zero_le_one
    ((one_le_div (sub_pos.mpr hlt)).mpr (sub_le_sub_right ht start))

namespace WaitingHomotopy

variable {initial terminal : C(A, X)} {start finish : ℝ}

/-- The actual continuous, piecewise extension map before packaging its endpoints.
Before the seam it is the ambient map composed with the actual radial homotopy;
after the seam it uses the original, unchanged time parameter. -/
def extendMap (H : WaitingHomotopy initial terminal finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z) (hlt : start < finish) :
    C(I × B, X) where
  toFun p := if (p.1 : ℝ) ≤ finish
    then f (R (waitingRamp start finish p.1, p.2))
    else H.toHomotopy (p.1, r p.2)
  continuous_toFun := by
    apply continuous_if_le
      (continuous_subtype_val.comp continuous_fst) continuous_const
    · exact (f.continuous.comp (R.continuous_toFun.comp
        (((waitingRamp start finish).continuous.comp continuous_fst).prodMk
          continuous_snd))).continuousOn
    · exact (H.toHomotopy.continuous_toFun.comp
        (continuous_fst.prodMk (r.continuous.comp continuous_snd))).continuousOn
    · intro p hp
      rw [waitingRamp_eq_one hlt (le_of_eq hp.symm), R.apply_one]
      exact (hf (r p.2)).trans (H.stationary p.1 (r p.2) (le_of_eq hp)).symm

/-- On the new waiting interval the extended map is exactly its initial map. -/
theorem extendMap_of_le_start (H : WaitingHomotopy initial terminal finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z) (hlt : start < finish)
    (t : I) (y : B) (ht : (t : ℝ) ≤ start) :
    H.extendMap j r R f hf hlt (t, y) = f y := by
  change (if (t : ℝ) ≤ finish then f (R (waitingRamp start finish t, y))
    else H.toHomotopy (t, r y)) = f y
  rw [ite_eq_left (ht.trans hlt.le), waitingRamp_eq_zero hlt ht, R.apply_zero]
  rfl

/-- At and after the old waiting time, the extension uses the old homotopy at
exactly the same parameter, with no concatenation-time rescaling. -/
theorem extendMap_of_finish_le (H : WaitingHomotopy initial terminal finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z) (hlt : start < finish)
    (t : I) (y : B) (ht : finish ≤ (t : ℝ)) :
    H.extendMap j r R f hf hlt (t, y) = H.toHomotopy (t, r y) := by
  change (if (t : ℝ) ≤ finish then f (R (waitingRamp start finish t, y))
    else H.toHomotopy (t, r y)) = H.toHomotopy (t, r y)
  by_cases h : (t : ℝ) ≤ finish
  · rw [ite_eq_left h, waitingRamp_eq_one hlt ht, R.apply_one]
    exact (hf (r y)).trans (H.stationary t (r y) h).symm
  · rw [ite_eq_right h]

/-- Extend a waiting homotopy using an actual radial homotopy and an actual
extension of the initial map. The terminal map is pulled back along `r`.
The retraction and strong fixed-point laws are needed only for exact restriction,
not for the existence or continuity of this extension. -/
def extendWaiting (H : WaitingHomotopy initial terminal finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z)
    (hstart : 0 ≤ start) (hlt : start < finish) (hfinish : finish ≤ 1) :
    WaitingHomotopy f (terminal.comp r) start where
  toHomotopy :=
    { toContinuousMap := H.extendMap j r R f hf hlt
      map_zero_left := fun y ↦ H.extendMap_of_le_start j r R f hf hlt 0 y hstart
      map_one_left := fun y ↦
        (H.extendMap_of_finish_le j r R f hf hlt 1 y hfinish).trans
          (H.toHomotopy.apply_one (r y)) }
  stationary := fun t y ht ↦ H.extendMap_of_le_start j r R f hf hlt t y ht

/-- The two-branch formula for the packaged extension. -/
theorem extendWaiting_apply (H : WaitingHomotopy initial terminal finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z)
    (hstart : 0 ≤ start) (hlt : start < finish) (hfinish : finish ≤ 1)
    (t : I) (y : B) :
    (H.extendWaiting j r R f hf hstart hlt hfinish).toHomotopy (t, y) =
      if (t : ℝ) ≤ finish then f (R (waitingRamp start finish t, y))
      else H.toHomotopy (t, r y) := rfl

/-- A strong radial deformation gives exact compatibility with the old homotopy
on the included space, at every time, including both endpoints and the seam. -/
theorem extendWaiting_restrict (H : WaitingHomotopy initial terminal finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z)
    (hstart : 0 ≤ start) (hlt : start < finish) (hfinish : finish ≤ 1)
    (hr : Function.LeftInverse r j) (hR : ∀ (t : I) (z : A), R (t, j z) = j z)
    (t : I) (z : A) :
    (H.extendWaiting j r R f hf hstart hlt hfinish).toHomotopy (t, j z) =
      H.toHomotopy (t, z) := by
  rw [extendWaiting_apply]
  by_cases ht : (t : ℝ) ≤ finish
  · rw [ite_eq_left ht, hR]
    exact (hf z).trans (H.stationary t z ht).symm
  · rw [ite_eq_right ht, hr z]

/-- In particular, extending a contraction preserves its actual constant endpoint. -/
def extendContraction {x : X} (H : WaitingHomotopy initial (ContinuousMap.const A x) finish)
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z)
    (hstart : 0 ≤ start) (hlt : start < finish) (hfinish : finish ≤ 1) :
    WaitingHomotopy f (ContinuousMap.const B x) start :=
  H.extendWaiting j r R f hf hstart hlt hfinish

end WaitingHomotopy

/-- Positive dyadic waiting times; stage zero waits through time `1 / 2`. -/
def dyadicWait (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

/-- The seed uses the waiting interval supplied by its open-cell contraction. -/
@[simp] theorem dyadicWait_zero : dyadicWait 0 = 1 / 2 := by
  simp [dyadicWait]

/-- Every finite stage retains a positive initial waiting interval. -/
theorem dyadicWait_pos (n : ℕ) : 0 < dyadicWait n :=
  pow_pos (by norm_num) _

/-- Every dyadic waiting time belongs to the unit interval. -/
theorem dyadicWait_le_one (n : ℕ) : dyadicWait n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-- Passing to the next stage leaves a nonempty radial time window. -/
theorem dyadicWait_succ_lt (n : ℕ) : dyadicWait (n + 1) < dyadicWait n := by
  change (1 / 2 : ℝ) ^ ((n + 1) + 1) < (1 / 2 : ℝ) ^ (n + 1)
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos (by norm_num) _) (by norm_num)

namespace WaitingHomotopy

/-- A dyadic extension step with its next waiting bound already proved. -/
def extendDyadic {initial terminal : C(A, X)} {n : ℕ}
    (H : WaitingHomotopy initial terminal (dyadicWait n))
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z) :
    WaitingHomotopy f (terminal.comp r) (dyadicWait (n + 1)) :=
  H.extendWaiting j r R f hf (dyadicWait_pos (n + 1)).le
    (dyadicWait_succ_lt n) (dyadicWait_le_one n)

/-- Exact same-time compatibility for the dyadic extension step. -/
theorem extendDyadic_restrict {initial terminal : C(A, X)} {n : ℕ}
    (H : WaitingHomotopy initial terminal (dyadicWait n))
    (j : C(A, B)) (r : C(B, A))
    (R : ContinuousMap.Homotopy (ContinuousMap.id B) (j.comp r))
    (f : C(B, X)) (hf : ∀ z, f (j z) = initial z)
    (hr : Function.LeftInverse r j) (hR : ∀ (t : I) (z : A), R (t, j z) = j z)
    (t : I) (z : A) :
    (H.extendDyadic j r R f hf).toHomotopy (t, j z) = H.toHomotopy (t, z) :=
  H.extendWaiting_restrict j r R f hf (dyadicWait_pos (n + 1)).le
    (dyadicWait_succ_lt n) (dyadicWait_le_one n) hr hR t z

end WaitingHomotopy

end Topology
