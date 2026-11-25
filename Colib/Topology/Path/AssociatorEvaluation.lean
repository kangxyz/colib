/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Pointwise evaluation of literal path operations

The actual nested path remains evaluated with the original path and
comparison clocks. Adapted from `Quillen/Aglib/Topology/Path/EvaluationOperations.lean`
and the operation formulas in `Quillen/Topology/Path/NullWordEvaluation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval

namespace Path.Evaluation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {a b c d : X} {a' b' c' d' : Y}

/-- Whole concatenation retains its original half cut under any pointwise evaluator. -/
theorem path_trans (f : X → Y) (p : Path a b) (q : Path b c)
    (p' : Path a' b') (q' : Path b' c')
    (hp : ∀ s, f (p s) = p' s) (hq : ∀ s, f (q s) = q' s) (s : unitInterval) :
    f ((p.trans q) s) = (p'.trans q') s := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

/-- The literal associator uses the same reparameterized nested path on both sides. -/
theorem transAssoc (f : X → Y) (p : Path a b) (q : Path b c) (w : Path c d)
    (p' : Path a' b') (q' : Path b' c') (w' : Path c' d')
    (hp : ∀ s, f (p s) = p' s) (hq : ∀ s, f (q s) = q' s)
    (hw : ∀ s, f (w s) = w' s) (r s : unitInterval) :
    f (Path.Homotopy.transAssoc p q w (r, s)) =
      Path.Homotopy.transAssoc p' q' w' (r, s) :=
  path_trans f p (q.trans w) p' (q'.trans w') hp (path_trans f q w q' w' hq hw) _

/-- Path reversal changes only the original path coordinate. -/
theorem path_symm (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (s : I) : f (p.symm s) = p'.symm s := hp _

/-- Comparison reversal does not reverse path time. -/
theorem comparison_symm (f : X → Y) {p q : Path a b} {p' q' : Path a' b'}
    (J : p.Homotopy q) (J' : p'.Homotopy q')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s)) (r s : I) :
    f (J.symm (r, s)) = J'.symm (r, s) := hJ _ s

/-- Vertical pasting changes comparison time at exactly the original half cut. -/
theorem comparison_trans (f : X → Y) {p q w : Path a b} {p' q' w' : Path a' b'}
    (J : p.Homotopy q) (K : q.Homotopy w)
    (J' : p'.Homotopy q') (K' : q'.Homotopy w')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (J.trans K (r, s)) = J'.trans K' (r, s) := by
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split_ifs
  · exact hJ _ s
  · exact hK _ s

/-- Horizontal pasting changes path time only, leaving comparison time independent. -/
theorem comparison_hcomp (f : X → Y)
    {p q : Path a b} {w z : Path b c} {p' q' : Path a' b'} {w' z' : Path b' c'}
    (J : p.Homotopy q) (K : w.Homotopy z)
    (J' : p'.Homotopy q') (K' : w'.Homotopy z')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (J.hcomp K (r, s)) = J'.hcomp K' (r, s) := by
  rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hJ r _
  · exact hK r _

/-- A constant comparison retains the complete supplied path. -/
theorem comparison_refl (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.refl p (r, s)) = Path.Homotopy.refl p' (r, s) := hp s

/-- The inverse-pair contraction retains its actual scalar formula. -/
theorem reflTransSymm (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.reflTransSymm p (r, s)) =
      Path.Homotopy.reflTransSymm p' (r, s) := hp _

/-- Initial-pause cancellation retains its actual reversed terminal-pause formula. -/
theorem reflTrans (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.reflTrans p (r, s)) = Path.Homotopy.reflTrans p' (r, s) := hp _

end Path.Evaluation
