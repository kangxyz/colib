/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactSimplex
public import Colib.Topology.Realization.Simplex

/-!
# Compact families on the original iterated Waldhausen prespectrum

Every point in the full reference nerve has a genuine characteristic simplex.
The compact family on a successor level is the stage family, and the level-zero
family evaluates the original loop at an independent time. On the specified
characteristic simplex both operations are exactly the native finite-simplex
family. Basepoints and the original structure coordinate are retained.

Adapted from `CommonReferenceNerveCompactFamily.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- Every actual nerve point has an original full-node characteristic-simplex representation. -/
theorem exists_parameter (y : |nerve (Codiscrete (Node F))|) :
    ∃ (k : ℕ) (N : Fin (k + 1) → Node F) (z : StdSimplex ℝ (Fin (k + 1))),
      parameter F N z = y := by
  obtain ⟨n, f, t, ht⟩ := realization_exists_simplex y
  cases n using SimplexCategory.rec with
  | _ k =>
    let c : Fin (k + 1) ⥤ Codiscrete (Node F) := SSet.yonedaEquiv f
    refine ⟨k, fun i ↦ (c.obj i).as, (SimplexCategory.toTopHomeo ⦋k⦌) t, ?_⟩
    change SSet.toTop.map (SSet.yonedaEquiv.symm c)
      ((SimplexCategory.toTopHomeo ⦋k⦌).symm ((SimplexCategory.toTopHomeo ⦋k⦌) t)) = y
    rw [Homeomorph.symm_apply_apply]
    change SSet.toTop.map (SSet.yonedaEquiv.symm (SSet.yonedaEquiv f)) t = y
    rw [Equiv.symm_apply_apply]
    exact ht

variable {T : Type v} [TopologicalSpace T] [CompactSpace T]

/-- Every compact parameter fixes the same original stage point. -/
theorem compactStageFamily_point (r : ℕ)
    (p : C(T, |nerve (Codiscrete (Node F))|)) (t : T) :
    compactStageFamily F r p (t, stagePoint r V) = stagePoint r W := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  exact (compactStageFamily_eq_simplex F r p N t z hz.symm _).trans
    (stageBarycentric_point F r N z)

/-- The actual input loop is evaluated at its own independent coordinate. -/
def compactLoopFamily (p : C(T, |nerve (Codiscrete (Node F))|)) :
    C(T × Path (stagePoint 0 V) (stagePoint 0 V), Path (stagePoint 0 W) (stagePoint 0 W)) where
  toFun z := {
    toFun s := compactStageFamily F 0 p (z.1, z.2 s)
    continuous_toFun := by fun_prop
    source' := by rw [Path.source]; exact compactStageFamily_point F 0 p z.1
    target' := by rw [Path.target]; exact compactStageFamily_point F 0 p z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (T × Path (stagePoint 0 V) (stagePoint 0 V)) × unitInterval ↦
      compactStageFamily F 0 p (z.1.1, z.1.2 z.2))
    fun_prop

/-- A compact nerve parameter acts continuously on every original prespectrum level. -/
def compactPrespectrumFamily (p : C(T, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    C(T × (prespectrum V).space n, (prespectrum W).space n) :=
  Nat.casesOn n (compactLoopFamily F p) (fun r ↦ compactStageFamily F r p)

/-- Every native level recovers the whole unchanged original finite-simplex family. -/
theorem compactPrespectrumFamily_eq_simplex
    (p : C(T, |nerve (Codiscrete (Node F))|)) {k : ℕ} (N : Fin (k + 1) → Node F)
    (t : T) (z : StdSimplex ℝ (Fin (k + 1))) (hp : p t = parameter F N z)
    (n : ℕ) (x : (prespectrum V).space n) :
    compactPrespectrumFamily F p n (t, x) = prespectrumSimplexFamily
      (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n (z, x) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext s
    exact (compactStageFamily_eq_simplex F 0 p N t z hp (x s)).trans
      (DFunLike.congr_fun (stageBarycentric_eq F 0 N) (z, x s))
  | succ r =>
    exact (compactStageFamily_eq_simplex F r p N t z hp x).trans
      (DFunLike.congr_fun (stageBarycentric_eq F r N) (z, x))

/-- Every actual native point is retained for every compact parameter and every level. -/
theorem compactPrespectrumFamily_point (p : C(T, |nerve (Codiscrete (Node F))|))
    (n : ℕ) (t : T) :
    compactPrespectrumFamily F p n (t, (prespectrum V).point n) =
      (prespectrum W).point n := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  exact (compactPrespectrumFamily_eq_simplex F p N t z hz.symm n _).trans
    (prespectrumSimplexFamily_point _ n z)

/-- One representation of the same nerve point preserves the independent structure time. -/
theorem compactPrespectrumFamily_structure (p : C(T, |nerve (Codiscrete (Node F))|))
    (n : ℕ) (t : T) (x : (prespectrum V).space n) (s : unitInterval) :
    compactPrespectrumFamily F p (n + 1) (t, (prespectrum V).structureMap n x s) =
      (prespectrum W).structureMap n (compactPrespectrumFamily F p n (t, x)) s := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  rw [compactPrespectrumFamily_eq_simplex F p N t z hz.symm,
    compactPrespectrumFamily_eq_simplex F p N t z hz.symm]
  exact prespectrumSimplexFamily_structure _ n z x s

/-- Level zero retains the original input-loop coordinate after compact stage evaluation. -/
theorem compactPrespectrumFamily_zero_apply (p : C(T, |nerve (Codiscrete (Node F))|))
    (t : T) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (s : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      compactPrespectrumFamily F p 0 (t, γ)) s = compactStageFamily F 0 p (t, γ s) := rfl

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
