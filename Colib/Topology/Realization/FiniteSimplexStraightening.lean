/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection
public import Colib.Topology.Realization.FiniteVertexStraightening
public import Colib.Topology.Realization.SimplexBoundaryFilling

/-!
# Face-compatible finite relative straightening

Construct finite tracks dimension by dimension. Each track extends the actual
previous face tracks, and all initially marked simplices are stationary. At
dimensions below the cutoff, actual homotopy vanishing supplies constant endpoints.

Adapted from `Quillen/Topology/Realization/FiniteSimplexStraightening.lean`
and `Quillen/Topology/Realization/SimplexStraighteningStep.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open Topology
open scoped Topology unitInterval

universe u

namespace Convexity.StdSimplex

variable {Z : Type u} [TopologicalSpace Z]

/-- Extend the prescribed side literally, choosing a constant endpoint exactly
in those dimensions in which the actual homotopy groups vanish. -/
theorem exists_simplex_straightening_step (n d : ℕ) (z : Z)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (f : C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : C(boundary d × I, Z))
    (hzero : ∀ b : boundary d, H (b, 0) = f b.val)
    (hone : d < n → ∀ b : boundary d, H (b, 1) = z) :
    ∃ g : C(StdSimplex ℝ (Fin (d + 1)), Z), ∃ K : f.Homotopy g,
      (∀ (b : boundary d) (t : I), K (t, b.val) = H (b, t)) ∧
      (d < n → g = ContinuousMap.const _ z) := by
  by_cases hd : d < n
  · obtain ⟨K, hK⟩ := exists_simplex_homotopy_of_boundary d (fun x ↦ hs x d hd)
      f (ContinuousMap.const _ z) H hzero (hone hd)
    exact ⟨ContinuousMap.const _ z, K, hK, fun _ ↦ rfl⟩
  · obtain ⟨g, K, hK⟩ := exists_simplex_homotopy_extension d f H hzero
    exact ⟨g, K, hK, fun h ↦ (hd h).elim⟩

/-- Make one relative straightening step simultaneously for a finite set of
actual singular simplices. Repeated occurrences of an equal map are the same
index. Already fixed simplices receive the literal stationary homotopy. -/
theorem exists_finite_simplex_straightening_step (n d : ℕ) (z : Z)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (S : Finset C(StdSimplex ℝ (Fin (d + 1)), Z))
    (F : Set C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : {s // s ∈ S} → C(boundary d × I, Z))
    (hzero : ∀ s (b : boundary d), H s (b, 0) = s.val b.val)
    (hone : d < n → ∀ s (b : boundary d), H s (b, 1) = z)
    (hfixed : ∀ s : {s // s ∈ S}, s.val ∈ F →
      ∀ (b : boundary d) (t : I), H s (b, t) = s.val b.val)
    (hcollapsed : ∀ s : {s // s ∈ S}, s.val ∈ F → d < n →
      s.val = ContinuousMap.const _ z) :
    ∃ g : {s // s ∈ S} → C(StdSimplex ℝ (Fin (d + 1)), Z),
      ∃ K : ∀ s : {s // s ∈ S}, s.val.Homotopy (g s), ∀ s : {s // s ∈ S},
        (∀ (b : boundary d) (t : I), K s (t, b.val) = H s (b, t)) ∧
        (d < n → g s = ContinuousMap.const _ z) ∧
        (s.val ∈ F → ∀ (t : I) (x : StdSimplex ℝ (Fin (d + 1))),
          K s (t, x) = s.val x) := by
  classical
  have hex (s : {s // s ∈ S}) :
      ∃ g : C(StdSimplex ℝ (Fin (d + 1)), Z), ∃ K : s.val.Homotopy g,
        (∀ (b : boundary d) (t : I), K (t, b.val) = H s (b, t)) ∧
        (d < n → g = ContinuousMap.const _ z) ∧
        (s.val ∈ F → ∀ (t : I) (x : StdSimplex ℝ (Fin (d + 1))),
          K (t, x) = s.val x) := by
    by_cases hmem : s.val ∈ F
    · exact ⟨s.val, ContinuousMap.Homotopy.refl s.val,
        fun b t ↦ (hfixed s hmem b t).symm, hcollapsed s hmem, fun _ _ _ ↦ rfl⟩
    · obtain ⟨g, K, hK, hg⟩ := exists_simplex_straightening_step n d z hs s.val
        (H s) (hzero s) (fun hd ↦ hone hd s)
      exact ⟨g, K, hK, hg, fun h ↦ (hmem h).elim⟩
  choose g K hside hconstant hstationary using hex
  exact ⟨g, K, fun s ↦ ⟨hside s, hconstant s, hstationary s⟩⟩

namespace PartialSimplexStraightening

variable {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}

/-- Zero-dimensional induction step, using the empty boundary and actual Pi 0. -/
theorem exists_first (n : ℕ) (z : Z) (S F : FiniteSimplexFamily Z)
    (hS : S.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS 1) := by
  let := isEmpty_boundary_zero
  let H : {s // s ∈ S 0} → C(boundary 0 × I, Z) :=
    fun _ ↦ ContinuousMap.const _ z
  obtain ⟨g, K, hK⟩ := exists_finite_simplex_straightening_step n 0 z hs (S 0) (F 0) H
    (fun _ b ↦ isEmptyElim b) (fun _ _ b ↦ isEmptyElim b)
    (fun _ _ b ↦ isEmptyElim b) (hcollapsed 0)
  let P := initial n z S F hS
  let L : {s // s ∈ S 0} → C(StdSimplex ℝ (Fin 1) × I, Z) :=
    fun s ↦ ⟨fun x ↦ K s (x.2, x.1), by fun_prop⟩
  refine ⟨{
    track := Function.update P.track 0 L
    bottom := ?_
    stationary := ?_
    face := by intro d hd; omega
    top := ?_ }⟩
  · intro d s x
    by_cases hd : d = 0
    · subst d
      simp [L]
    · simpa [Function.update_of_ne hd] using P.bottom d s x
  · intro d s hs x t
    by_cases hd : d = 0
    · subst d
      simpa [L] using (hK s).2.2 hs t x
    · simpa [Function.update_of_ne hd] using P.stationary d s hs x t
  · intro d hd hn s x
    have hd0 : d = 0 := by omega
    subst d
    simp [L, (hK s).2.1 hn]

/-- Advance one positive dimension. Above the cutoff only HEP is used. -/
theorem exists_succ (d : ℕ)
    (P : PartialSimplexStraightening n z S F hS (d + 1))
    (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ e (s : {s // s ∈ S e}), s.val ∈ F e → e < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS (d + 2)) := by
  choose H hH using P.exists_boundary d
  have hzero (s : {s // s ∈ S (d + 1)}) (b : boundary (d + 1)) :
      H s (b, 0) = s.val b.val := by
    obtain ⟨⟨i, x, t⟩, ht⟩ := simplexFaceCylinderCover_surjective d (b, (0 : I))
    have hb : simplexBoundaryFace d i x = b := congrArg Prod.fst ht
    rw [← hb, hH, P.bottom]
    rfl
  have hone (hdn : d + 1 < n) (s : {s // s ∈ S (d + 1)})
      (b : boundary (d + 1)) : H s (b, 1) = z := by
    obtain ⟨⟨i, x, t⟩, ht⟩ := simplexFaceCylinderCover_surjective d (b, (1 : I))
    have hb : simplexBoundaryFace d i x = b := congrArg Prod.fst ht
    rw [← hb, hH]
    exact P.top d (by omega) (by omega) _ x
  have hfixed (s : {s // s ∈ S (d + 1)}) (hsF : s.val ∈ F (d + 1))
      (b : boundary (d + 1)) (t : I) : H s (b, t) = s.val b.val := by
    obtain ⟨⟨i, x, u⟩, hu⟩ := simplexFaceCylinderCover_surjective d (b, t)
    have hb : simplexBoundaryFace d i x = b := congrArg Prod.fst hu
    rw [← hb, hH, P.stationary d (hS.face s i) (hF d s.val hsF i)]
    rfl
  obtain ⟨g, K, hK⟩ := exists_finite_simplex_straightening_step n (d + 1) z hs
    (S (d + 1)) (F (d + 1)) H hzero hone hfixed (hcollapsed (d + 1))
  let L : {s // s ∈ S (d + 1)} → C(StdSimplex ℝ (Fin (d + 2)) × I, Z) :=
    fun s ↦ ⟨fun x ↦ K s (x.2, x.1), by fun_prop⟩
  refine ⟨{
    track := Function.update P.track (d + 1) L
    bottom := ?_
    stationary := ?_
    face := ?_
    top := ?_ }⟩
  · intro e s x
    by_cases he : e = d + 1
    · subst e
      simp [L]
    · simpa [Function.update_of_ne he] using P.bottom e s x
  · intro e s hsF x t
    by_cases he : e = d + 1
    · subst e
      simpa [L] using (hK s).2.2 hsF t x
    · simpa [Function.update_of_ne he] using P.stationary e s hsF x t
  · intro e he s i x t
    by_cases hed : e = d
    · subst e
      have hne : d ≠ d + 1 := by omega
      simp only [Function.update_self, Function.update_of_ne hne]
      exact ((hK s).1 (simplexBoundaryFace d i x) t).trans (hH s i x t)
    · have he1 : e + 1 ≠ d + 1 := by omega
      have he0 : e ≠ d + 1 := by omega
      simpa only [Function.update_of_ne he1, Function.update_of_ne he0] using
        P.face e (by omega) s i x t
  · intro e he hn s x
    by_cases hed : e = d + 1
    · subst e
      simp [L, (hK s).2.1 hn]
    · simpa only [Function.update_of_ne hed] using P.top e (by omega) hn s x

end PartialSimplexStraightening

/-- Full relative finite straightening through any chosen dimension bound.
There are no assumed compatibility certificates: all tracks are constructed
from actual low homotopy vanishing and boundary HEP. -/
theorem exists_finite_simplex_straightening (n N : ℕ) (z : Z)
    (S F : FiniteSimplexFamily Z) (hS : S.FaceClosed) (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS N) := by
  induction N with
  | zero => exact ⟨PartialSimplexStraightening.initial n z S F hS⟩
  | succ N ih =>
    cases N with
    | zero => exact PartialSimplexStraightening.exists_first n z S F hS hs hcollapsed
    | succ d =>
      obtain ⟨P⟩ := ih
      exact P.exists_succ d hF hs hcollapsed

/-- Path connectedness supplies degree zero; only positive homotopy groups
strictly below the cutoff are additional assumptions. -/
theorem exists_finite_simplex_straightening_of_pathConnected [PathConnectedSpace Z]
    (n N : ℕ) (z : Z) (S F : FiniteSimplexFamily Z)
    (hS : S.FaceClosed) (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS N) := by
  apply exists_finite_simplex_straightening n N z S F hS hF _ hcollapsed
  intro x k hk
  cases k with
  | zero => exact subsingleton_homotopyGroup_zero x
  | succ k => exact hs x (k + 1) (by omega) hk

end Convexity.StdSimplex
