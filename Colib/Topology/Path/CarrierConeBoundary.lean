/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Topology.Path.CarrierSquareDescent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Cone boundaries and evaluation

For a carrier square with a constant terminal edge, first take the literal three-side boundary
and then remove its terminal pause. The calculation uses the original collapse and original
`Path.Homotopy.transRefl` time, including under pointwise evaluation.

Adapted from `CarrierSquareBoundary.lean` and `CarrierSquareBoundaryEvaluation.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v

namespace Topology.CarrierPathSquare
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

section Boundary
variable {a b c : X} {old : Path a c} {new : Path b c} {move : Path a b}

/-- Keep the original terminal pause before cancellation, including its full square interior. -/
def Square.pausedConeBoundary (Q : Square old new move (Path.refl c)) :
    old.Homotopy ((move.trans new).trans (Path.refl c)) :=
  Q.toBoundary.cast rfl (congrArg (fun z : Path c c ↦ (move.trans new).trans z)
    (show (Path.refl c).symm = Path.refl c by ext s; rfl))

/-- Exact carrier counterpart of original conePasting: collapse, boundary cast, then transRefl. -/
def Square.coneBoundary (Q : Square old new move (Path.refl c)) :
    old.Homotopy (move.trans new) :=
  Q.pausedConeBoundary.trans (Path.Homotopy.transRefl (move.trans new))

/-- The first half is the original collapsed square; the second is the original pause removal. -/
theorem Square.coneBoundary_apply (Q : Square old new move (Path.refl c))
    (r s : unitInterval) :
    Q.coneBoundary (r, s) =
      if h : (r : ℝ) ≤ 1 / 2 then
        Q.parameter (ThreeSideSquare.collapse
          (⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, h⟩⟩, s))
      else
        Path.Homotopy.transRefl (move.trans new)
          (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, r.2.2⟩⟩, s) :=
  Path.Homotopy.trans_apply Q.pausedConeBoundary
    (Path.Homotopy.transRefl (move.trans new)) (r, s)

end Boundary

section Evaluation
/-- Whole path pointwise equality survives the original terminal-pause cancellation clock. -/
private theorem transRefl_natural {a b : X} {c d : Y} (p : Path a b) (q : Path c d)
    (f : X → Y) (h : ∀ s, f (p s) = q s) (r s : unitInterval) :
    f (Path.Homotopy.transRefl p (r, s)) = Path.Homotopy.transRefl q (r, s) :=
  h _

private theorem trans_natural {a b c : X} {d e g : Y}
    (p : Path a b) (q : Path b c) (p' : Path d e) (q' : Path e g)
    (f : X → Y) (hp : ∀ s, f (p s) = p' s) (hq : ∀ s, f (q s) = q' s)
    (s : unitInterval) : f ((p.trans q) s) = (p'.trans q') s := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

variable {a b c : X} {d e g : Y}
  {old : Path a c} {new : Path b c} {move : Path a b}
  {old' : Path d g} {new' : Path e g} {move' : Path d e}

/-- Full cone-square evaluation preserves both halves of collapse followed by pause removal. -/
theorem Square.coneBoundary_natural (Q : Square old new move (Path.refl c))
    (S : Square old' new' move' (Path.refl g)) (f : X → Y)
    (h : ∀ r s, f (Q.parameter (r, s)) = S.parameter (r, s)) (r s : unitInterval) :
    f (Q.coneBoundary (r, s)) = S.coneBoundary (r, s) := by
  have hm : ∀ t, f (move t) = move' t := fun t ↦
    (congrArg f (Q.left t)).symm.trans ((h t 0).trans (S.left t))
  have hn : ∀ t, f (new t) = new' t := fun t ↦
    (congrArg f (Q.at_one t)).symm.trans ((h 1 t).trans (S.at_one t))
  rw [Square.coneBoundary_apply, Square.coneBoundary_apply]
  split_ifs
  · exact h _ _
  · exact transRefl_natural (move.trans new) (move'.trans new') f
      (trans_natural move new move' new' f hm hn) _ s

end Evaluation

end Topology.CarrierPathSquare
