/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Mathlib.Topology.Homotopy.Path

/-!
# Scalar evaluation of a pasted triple comparison

The two horizontal composites are pasted around the middle comparison, with
the left composite traversed backwards in comparison time. Both time
coordinates are preserved before specializing to any geometric family.

Implementation provenance: `Quillen/Topology/Prespectrum/TripleOperationEvaluation.lean`
and `Quillen/Waldhausen/SConstruction/Iterated/ScalarTripleEvaluation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CategoryTheory
open scoped Topology unitInterval

universe u v

namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy

section

variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F} {H K L : Homotopy f g}

theorem level_trans_apply (J : H.RelHomotopy K) (J' : K.RelHomotopy L)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        J.level n (⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨r.2.1, hr⟩⟩, (s, x))
      else J'.level n (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

private theorem level_symm_apply (J : H.RelHomotopy K) (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    J.symm.level n (r, (s, x)) = J.level n (unitInterval.symm r, (s, x)) := rfl

private theorem level_hcomp_apply {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K') (n : ℕ) (r s : unitInterval)
    (x : E.space n) :
    (J.hcomp L).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨s.2.1, hs⟩⟩, x))
      else L.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

private theorem level_cast_apply {f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (hf : f = f') (hg : g = g')
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.cast hf hg).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl

end

/-- The scalar five-piece pasting evaluates to the same relative homotopy at both times. -/
theorem scalar_triple_evaluation {Z : Type v} [TopologicalSpace Z]
    {E F : LoopPrespectrum.{u}} {a b c d : Z}
    {p₀ p₀' : Path a b} {p₁ p₁' : Path b c}
    {q₀ q₀' : Path a d} {q₁ q₁' : Path d c}
    {f g h f' g' h' : E ⟶ F}
    {H₀ H₀' : Homotopy f g} {H₁ H₁' : Homotopy g h}
    {K₀ K₀' : Homotopy f' g'} {K₁ K₁' : Homotopy g' h'}
    (n : ℕ) (ev : Z → E.space n → F.space n)
    (JA : p₀.Homotopy p₀') (JB : p₁.Homotopy p₁')
    (JM : (p₀.trans p₁).Homotopy (q₀.trans q₁))
    (JR : q₀.Homotopy q₀') (JS : q₁.Homotopy q₁')
    (hf : f' = f) (hh : h' = h)
    (A : H₀.RelHomotopy H₀') (B : H₁.RelHomotopy H₁')
    (R : K₀.RelHomotopy K₀') (S : K₁.RelHomotopy K₁')
    (M : (H₀.trans H₁).RelHomotopy ((K₀.trans K₁).cast hf hh))
    (eA : ∀ r s x, ev (JA (r, s)) x = A.level n (r, (s, x)))
    (eB : ∀ r s x, ev (JB (r, s)) x = B.level n (r, (s, x)))
    (eM : ∀ r s x, ev (JM (r, s)) x = M.level n (r, (s, x)))
    (eR : ∀ r s x, ev (JR (r, s)) x = R.level n (r, (s, x)))
    (eS : ∀ r s x, ev (JS (r, s)) x = S.level n (r, (s, x)))
    (r s : unitInterval) (x : E.space n) :
    ev (((JA.hcomp JB).symm.trans (JM.trans (JR.hcomp JS))) (r, s)) x =
      ((A.hcomp B).symm.trans (M.trans ((R.hcomp S).cast hf hh))).level n (r, (s, x)) := by
  rw [Path.Homotopy.trans_apply, Homotopy.RelHomotopy.level_trans_apply]
  split
  · rw [Homotopy.RelHomotopy.level_symm_apply]
    change ev ((JA.hcomp JB) (_, s)) x = _
    rw [Path.Homotopy.hcomp_apply, Homotopy.RelHomotopy.level_hcomp_apply]
    split
    · exact eA _ _ x
    · exact eB _ _ x
  · rw [Path.Homotopy.trans_apply, Homotopy.RelHomotopy.level_trans_apply]
    split
    · exact eM _ s x
    · rw [Homotopy.RelHomotopy.level_cast_apply, Path.Homotopy.hcomp_apply,
        Homotopy.RelHomotopy.level_hcomp_apply]
      split
      · exact eR _ _ x
      · exact eS _ _ x

end Topology.LoopPrespectrum.Homotopy.RelHomotopy
