/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactStage

/-!
# Compact common-reference evaluation at every original prespectrum level

Continuity comes from a genuinely finite compact carrier. For the adjacent-level law a single
original simplex represents the common point at both levels; the original structure time is
not one of the carrier coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Simplicial Topology unitInterval

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
variable {T U : Type v} [TopologicalSpace T] [TopologicalSpace U]
  [CompactSpace T] [CompactSpace U]

/-- The original loop in degree zero and the original realized stages in higher degrees. -/
def compactPrespectrumFamily (p : C(T, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    C(T × (prespectrum V).space n, (prespectrum W).space n) :=
  Nat.casesOn n (compactLoopZeroFamily F p) (fun r ↦ compactStageFamily F r p)

/-- Different compact parameters agreeing at a point give the exact same evaluated family. -/
theorem compactPrespectrumFamily_of_point_eq (n : ℕ)
    (p : C(T, |nerve (Codiscrete (Node F))|))
    (q : C(U, |nerve (Codiscrete (Node F))|)) (t : T) (s : U) (h : p t = q s)
    (x : (prespectrum V).space n) :
    compactPrespectrumFamily F p n (t, x) = compactPrespectrumFamily F q n (s, x) := by
  cases n with
  | zero => exact compactLoopZeroFamily_of_point_eq F p q t s h x
  | succ r => exact compactStageFamily_of_point_eq F r p q t s h x

/-- The unchanged original stage point is fixed by every parameter. -/
theorem compactStageFamily_point (r : ℕ)
    (p : C(T, |nerve (Codiscrete (Node F))|)) (t : T) :
    compactStageFamily F r p (t, stagePoint r V) = stagePoint r W := by
  obtain ⟨k, c, z, h⟩ := exists_chain F (p t)
  exact (compactStageFamily_eq_chain F r p c t z h _).trans
    (stageSimplexRealization_fixed_point r (chain F c) z)

/-- The original prespectrum points are fixed at every degree. -/
theorem compactPrespectrumFamily_point (p : C(T, |nerve (Codiscrete (Node F))|))
    (n : ℕ) (t : T) :
    compactPrespectrumFamily F p n (t, (prespectrum V).point n) = (prespectrum W).point n := by
  cases n with
  | zero =>
    change compactLoopZeroFamily F p (t, Path.refl (stagePoint 0 V)) =
      Path.refl (stagePoint 0 W)
    apply Path.ext
    funext s
    exact compactStageZeroFamily_point F p t
  | succ r => exact compactStageFamily_point F r p t

/-- One original finite chain represents the same carrier on both sides of suspension. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceNerveCompactFamily.lean:103-114"
  "adaptation" "Exact adjacent-level law with one shared carrier and independent structure time."]
theorem compactPrespectrumFamily_structure (p : C(T, |nerve (Codiscrete (Node F))|))
    (n : ℕ) (t : T) (x : (prespectrum V).space n) (s : unitInterval) :
    compactPrespectrumFamily F p (n + 1) (t, (prespectrum V).structureMap n x s) =
      (prespectrum W).structureMap n (compactPrespectrumFamily F p n (t, x)) s := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    change compactStageFamily F 0 p (t, x s) = (compactLoopZeroFamily F p (t, x)) s
    exact (DFunLike.congr_fun (compactStageFamily_zero F p) (t, x s)).trans
      (compactLoopZeroFamily_apply F p t x s).symm
  | succ r =>
    change compactStageFamily F (r + 1) p (t, stageLoopMap r V x s) =
      stageLoopMap r W (compactStageFamily F r p (t, x)) s
    obtain ⟨k, c, z, h⟩ := exists_chain F (p t)
    rw [compactStageFamily_eq_chain F (r + 1) p c t z h,
      compactStageFamily_eq_chain F r p c t z h]
    exact stageSimplexRealization_structure r (chain F c) z s x

/-- Level zero retains the same input loop and its own evaluation time. -/
theorem compactPrespectrumFamily_zero_apply (p : C(T, |nerve (Codiscrete (Node F))|))
    (t : T) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (s : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      compactPrespectrumFamily F p 0 (t, γ)) s = compactStageZeroFamily F p (t, γ s) := by
  change (compactLoopZeroFamily F p (t, γ)) s = _
  exact compactLoopZeroFamily_apply F p t γ s

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
