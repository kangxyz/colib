/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.ScalarRectangleLiftOps
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding
public import Colib.Topology.Prespectrum.HomotopySquarePathPasting
public import Colib.Topology.Prespectrum.HomotopySquareBoundary
public import Colib.Topology.Prespectrum.ScalarTripleEvaluation

/-! Exact scalar square operations used in the original raw Bass identity.
Adapted from Quillen `SimplexLiftSquareOperations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
  {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}

/-- A scalar square with its four literal path boundaries. -/
structure ParameterSquare (p₀ : Path a₀ b₀) (p₁ : Path a₁ b₁)
    (l : Path a₀ a₁) (m : Path b₀ b₁) where
  /-- The continuous two-coordinate simplex parameter with the four specified path boundaries. -/
  parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1)))
  at_zero (s : unitInterval) : parameter (0, s) = p₀ s
  at_one (s : unitInterval) : parameter (1, s) = p₁ s
  left (r : unitInterval) : parameter (r, 0) = l r
  right (r : unitInterval) : parameter (r, 1) = m r

private theorem path_pasted_left (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (r : unitInterval) :
    ((l.trans p).trans m.symm) (ThreeSideSquare.leftTime r) = l r := by
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · congr 1
      apply Subtype.ext
      dsimp [ThreeSideSquare.leftTime]
      ring
    · rename_i h
      dsimp [ThreeSideSquare.leftTime] at h
      linarith [r.2.2]
  · rename_i h
    dsimp [ThreeSideSquare.leftTime] at h
    linarith [r.2.2]

private theorem path_pasted_top (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (s : unitInterval) :
    ((l.trans p).trans m.symm) (ThreeSideSquare.topTime s) = p s := by
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · rename_i h
      have hs : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        dsimp [ThreeSideSquare.topTime] at h
        linarith [s.2.1]
      subst s
      trans l 1
      · congr 1
        apply Subtype.ext
        norm_num [ThreeSideSquare.topTime]
      · exact l.target.trans p.source.symm
    · congr 1
      apply Subtype.ext
      dsimp [ThreeSideSquare.topTime]
      ring
  · rename_i h
    dsimp [ThreeSideSquare.topTime] at h
    linarith [s.2.2]

private theorem path_pasted_right (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (r : unitInterval) :
    ((l.trans p).trans m.symm) (ThreeSideSquare.rightTime r) = m r := by
  rw [Path.trans_apply]
  split
  · rename_i h
    have hr : r = 1 := by
      apply Subtype.ext
      change (r : ℝ) = 1
      dsimp [ThreeSideSquare.rightTime] at h
      linarith [r.2.2]
    subst r
    trans (l.trans p) 1
    · congr 1
      apply Subtype.ext
      norm_num [ThreeSideSquare.rightTime]
    · exact (l.trans p).target.trans m.target.symm
  · change m (unitInterval.symm _) = _
    congr 1
    apply Subtype.ext
    dsimp [ThreeSideSquare.rightTime, unitInterval.symm]
    ring

private theorem boundary_time_cases (s : unitInterval) :
    (∃ r, s = ThreeSideSquare.leftTime r) ∨
    (∃ r, s = ThreeSideSquare.topTime r) ∨
    (∃ r, s = ThreeSideSquare.rightTime r) := by
  by_cases h : (s : ℝ) ≤ 1 / 4
  · left
    refine ⟨⟨4 * s, by constructor <;> linarith [s.2.1]⟩, ?_⟩
    apply Subtype.ext
    dsimp [ThreeSideSquare.leftTime]
    ring
  · by_cases h' : (s : ℝ) ≤ 1 / 2
    · right; left
      refine ⟨⟨4 * s - 1, by constructor <;> linarith⟩, ?_⟩
      apply Subtype.ext
      dsimp [ThreeSideSquare.topTime]
      ring
    · right; right
      refine ⟨⟨2 - 2 * s, by constructor <;> linarith [s.2.2]⟩, ?_⟩
      apply Subtype.ext
      dsimp [ThreeSideSquare.rightTime]
      ring

/-- The actual collapsed upper boundary is the exact original left-associated path pasting. -/
theorem ParameterSquare.collapse_top (Q : ParameterSquare p₀ p₁ l m) (s : unitInterval) :
    Q.parameter (ThreeSideSquare.collapse (1, s)) =
      ((l.trans p₁).trans m.symm) s := by
  rcases boundary_time_cases s with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [ThreeSideSquare.collapse_leftTime]
    exact (Q.left r).trans (path_pasted_left p₁ l m r).symm
  · rw [ThreeSideSquare.collapse_topTime]
    exact (Q.at_one r).trans (path_pasted_top p₁ l m r).symm
  · rw [ThreeSideSquare.collapse_rightTime]
    exact (Q.right r).trans (path_pasted_right p₁ l m r).symm

/-- Extract the scalar boundary by the same parameter collapse as the native moving square. -/
def ParameterSquare.toBoundary (Q : ParameterSquare p₀ p₁ l m) :
    p₀.Homotopy ((l.trans p₁).trans m.symm) where
  toFun z := Q.parameter (ThreeSideSquare.collapse z)
  continuous_toFun := Q.parameter.continuous.comp ThreeSideSquare.continuous_collapse
  map_zero_left s := by rw [ThreeSideSquare.collapse_zero]; exact Q.at_zero s
  map_one_left := Q.collapse_top
  prop' r s hs := by
    change Q.parameter (ThreeSideSquare.collapse (r, s)) = p₀ s
    rcases hs with hs | hs
    · subst s
      rw [ThreeSideSquare.collapse_left]
      exact Q.at_zero 0
    · subst s
      rw [ThreeSideSquare.collapse_right]
      exact Q.at_zero 1

variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (S : ModelSimplex V W k)
  {f₀ g₀ f₁ g₁ : prespectrum V ⟶ prespectrum W}
  {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
  {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}

/-- Literal whole-family equality to the specified native square. -/
def SquareLift (Q : ParameterSquare p₀ p₁ l m) (N : H₀.Square H₁ L M) : Prop :=
  ∀ n r s x, prespectrumSimplexFamily S n (Q.parameter (r, s), x) =
    N.level n (r, (s, x))

/-- Boundary extraction preserves every value of the original native square. -/
theorem SquareLift.toBoundary {Q : ParameterSquare p₀ p₁ l m} {N : H₀.Square H₁ L M}
    (hQ : SquareLift S Q N) : HomotopyLift S Q.toBoundary N.toBoundary := by
  intro n r s x
  exact hQ n (ThreeSideSquare.collapse (r, s)).1
    (ThreeSideSquare.collapse (r, s)).2 x

/-- Parameter reversal retains the entire original square, not just its sides. -/
def ParameterSquare.reversePaths (Q : ParameterSquare p₀ p₁ l m) :
    ParameterSquare p₀.symm p₁.symm m l where
  parameter := ⟨fun z ↦ Q.parameter (z.1, unitInterval.symm z.2), by fun_prop⟩
  at_zero s := Q.at_zero (unitInterval.symm s)
  at_one s := Q.at_one (unitInterval.symm s)
  left r := by simpa using Q.right r
  right r := by simpa using Q.left r

/-- Descent through the native three-side quotient gives a square with exact scalar sides. -/
def ParameterSquare.ofBoundary (J : p₀.Homotopy ((l.trans p₁).trans m.symm)) :
    ParameterSquare p₀ p₁ l m where
  parameter := collapsed J
  at_zero s := by
    have h := collapsed_collapse J (0, s)
    rw [ThreeSideSquare.collapse_zero] at h
    exact h.trans (J.apply_zero s)
  at_one s := by
    have h := collapsed_collapse J (1, ThreeSideSquare.topTime s)
    rw [ThreeSideSquare.collapse_topTime] at h
    exact h.trans ((J.apply_one _).trans (path_pasted_top p₁ l m s))
  left r := by
    have h := collapsed_collapse J (1, ThreeSideSquare.leftTime r)
    rw [ThreeSideSquare.collapse_leftTime] at h
    exact h.trans ((J.apply_one _).trans (path_pasted_left p₁ l m r))
  right r := by
    have h := collapsed_collapse J (1, ThreeSideSquare.rightTime r)
    rw [ThreeSideSquare.collapse_rightTime] at h
    exact h.trans ((J.apply_one _).trans (path_pasted_right p₁ l m r))

variable {c₀ c₁ : StdSimplex ℝ (Fin (k + 1))}
  {q₀ : Path b₀ c₀} {q₁ : Path b₁ c₁} {j : Path c₀ c₁}

/-- Exchange the moving and path parameters of a scalar square. -/
def ParameterSquare.swapHomotopy (Q : ParameterSquare p₀ p₁ l m) :
    l.toContinuousMap.Homotopy m.toContinuousMap where
  toFun z := Q.parameter (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := Q.left r
  map_one_left r := Q.right r

/-- Paste scalar moving squares using precisely the native dyadic path subdivision. -/
def ParameterSquare.pastePaths (Q : ParameterSquare p₀ p₁ l m)
    (R : ParameterSquare q₀ q₁ m j) :
    ParameterSquare (p₀.trans q₀) (p₁.trans q₁) l j where
  parameter := ⟨fun z ↦ ((Q.swapHomotopy).trans (R.swapHomotopy)) (z.2, z.1), by fun_prop⟩
  at_zero s := by
    change (Q.swapHomotopy.trans R.swapHomotopy) (s, 0) = (p₀.trans q₀) s
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact Q.at_zero _
    · exact R.at_zero _
  at_one s := by
    change (Q.swapHomotopy.trans R.swapHomotopy) (s, 1) = (p₁.trans q₁) s
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact Q.at_one _
    · exact R.at_one _
  left r := ((Q.swapHomotopy).trans (R.swapHomotopy)).apply_zero r
  right r := ((Q.swapHomotopy).trans (R.swapHomotopy)).apply_one r

theorem ParameterSquare.pastePaths_apply (Q : ParameterSquare p₀ p₁ l m)
    (R : ParameterSquare q₀ q₁ m j) (r s : unitInterval) :
    (Q.pastePaths R).parameter (r, s) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        Q.parameter (r, ⟨2 * s,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩)
      else R.parameter (r, ⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

/-- Transport only the four scalar boundary paths, preserving the entire square parameter. -/
def ParameterSquare.ofBoundaryPaths
    {a₀' b₀' a₁' b₁' : StdSimplex ℝ (Fin (k + 1))}
    (Q : ParameterSquare p₀ p₁ l m) (p₀' : Path a₀' b₀') (p₁' : Path a₁' b₁')
    (l' : Path a₀' a₁') (m' : Path b₀' b₁')
    (h₀ : ∀ t, p₀' t = p₀ t) (h₁ : ∀ t, p₁' t = p₁ t)
    (hl : ∀ t, l' t = l t) (hm : ∀ t, m' t = m t) :
    ParameterSquare p₀' p₁' l' m' where
  parameter := Q.parameter
  at_zero t := (Q.at_zero t).trans (h₀ t).symm
  at_one t := (Q.at_one t).trans (h₁ t).symm
  left t := (Q.left t).trans (hl t).symm
  right t := (Q.right t).trans (hm t).symm

/-- Map every scalar point through the actual affine simplex face. -/
def ParameterSquare.reindex {d : ℕ} (Q : ParameterSquare p₀ p₁ l m)
    (α : SimplexCategory.mk k ⟶ SimplexCategory.mk d) :
    ParameterSquare (p₀.map (StdSimplex.continuous_map ℝ α.toOrderHom))
      (p₁.map (StdSimplex.continuous_map ℝ α.toOrderHom))
      (l.map (StdSimplex.continuous_map ℝ α.toOrderHom))
      (m.map (StdSimplex.continuous_map ℝ α.toOrderHom)) where
  parameter := ⟨fun z ↦ StdSimplex.map α.toOrderHom (Q.parameter z), by fun_prop⟩
  at_zero t := congrArg (StdSimplex.map α.toOrderHom) (Q.at_zero t)
  at_one t := congrArg (StdSimplex.map α.toOrderHom) (Q.at_one t)
  left t := congrArg (StdSimplex.map α.toOrderHom) (Q.left t)
  right t := congrArg (StdSimplex.map α.toOrderHom) (Q.right t)

section Postcomposition
variable {Z : LoopPrespectrum.{u}} (c : Z ⟶ prespectrum W)

/-- Concatenate original tracks before the unchanged postmap, with both dyadic halves exact. -/
theorem PathLift.postcompTrans
    {a b d : StdSimplex ℝ (Fin (k + 1))} {p : Path a b} {q : Path b d}
    {f g h : prespectrum V ⟶ Z} {H : Homotopy f g} {K : Homotopy g h}
    (hp : PathLift S p (H.postcomp c)) (hq : PathLift S q (K.postcomp c)) :
    PathLift S (p.trans q) ((H.trans K).postcomp c) := by
  intro n t x
  change prespectrumSimplexFamily S n ((p.trans q) t, x) =
    c.map n (((H.levelHomotopy n).trans (K.levelHomotopy n)) (t, x))
  rw [Path.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hp n _ x
  · exact hq n _ x

/-- Native relative concatenation survives an unchanged postmap, with the exact original times. -/
theorem HomotopyLift.postcompTrans
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q z : Path a b}
    {J : p.Homotopy q} {K : q.Homotopy z}
    {f g : prespectrum V ⟶ Z} {H H' H'' : Homotopy f g}
    {N : H.RelHomotopy H'} {N' : H'.RelHomotopy H''}
    (hJ : HomotopyLift S J (N.postcomp c))
    (hK : HomotopyLift S K (N'.postcomp c)) :
    HomotopyLift S (J.trans K) ((N.trans N').postcomp c) := by
  intro n r s x
  change prespectrumSimplexFamily S n ((J.trans K) (r, s), x) =
    c.map n ((N.trans N').level n (r, (s, x)))
  rw [Path.Homotopy.trans_apply, Homotopy.RelHomotopy.level_trans_apply]
  split
  · exact hJ n _ s x
  · exact hK n _ s x

private theorem native_hcomp_values {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
    {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K')
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.hcomp L).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else L.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

/-- Horizontal pasting retains an unchanged postmap outside the actual native pasting. -/
theorem HomotopyLift.postcompHcomp
    {a b d : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} {p' q' : Path b d}
    {J : p.Homotopy q} {K : p'.Homotopy q'}
    {f g h : prespectrum V ⟶ Z} {H H' : Homotopy f g} {L L' : Homotopy g h}
    {N : H.RelHomotopy H'} {N' : L.RelHomotopy L'}
    (hJ : HomotopyLift S J (N.postcomp c))
    (hK : HomotopyLift S K (N'.postcomp c)) :
    HomotopyLift S (J.hcomp K) ((N.hcomp N').postcomp c) := by
  intro n r s x
  change prespectrumSimplexFamily S n ((J.hcomp K) (r, s), x) =
    c.map n ((N.hcomp N').level n (r, (s, x)))
  rw [Path.Homotopy.hcomp_apply, native_hcomp_values]
  split
  · exact hJ n r _ x
  · exact hK n r _ x

/-- The original terminal constant-half contraction is preserved before postcomposition. -/
theorem PathLift.postcompTransRefl
    {a b : StdSimplex ℝ (Fin (k + 1))} {p : Path a b}
    {f g : prespectrum V ⟶ Z} {H : Homotopy f g}
    (hp : PathLift S p (H.postcomp c)) :
    HomotopyLift S (Path.Homotopy.transRefl p) ((Homotopy.RelHomotopy.transRefl H).postcomp c) := by
  intro n r s x
  change prespectrumSimplexFamily S n (Path.Homotopy.transRefl p (r, s), x) =
    c.map n (((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap (r, (s, x)))
  rw [native_terminal_level]
  exact hp n _ x

/-- The original initial constant-half contraction is preserved before postcomposition. -/
theorem PathLift.postcompReflTrans
    {a b : StdSimplex ℝ (Fin (k + 1))} {p : Path a b}
    {f g : prespectrum V ⟶ Z} {H : Homotopy f g}
    (hp : PathLift S p (H.postcomp c)) :
    HomotopyLift S (Path.Homotopy.reflTrans p) ((Homotopy.RelHomotopy.reflTrans H).postcomp c) := by
  intro n r s x
  change prespectrumSimplexFamily S n (Path.Homotopy.reflTrans p (r, s), x) =
    c.map n (((Homotopy.RelHomotopy.reflTrans H).level n).toContinuousMap (r, (s, x)))
  rw [native_initial_level]
  exact (HomotopyLift.symmPath S
    (PathLift.postcompTransRefl S c (H := H.symm) (PathLift.symm S hp))) n r s x

/-- Collapse the exact relative comparison before its original postmap, not a replacement square. -/
theorem HomotopyLift.postcompOfBoundary
    {J : p₀.Homotopy ((l.trans p₁).trans m.symm)}
    {f₀ g₀ f₁ g₁ : prespectrum V ⟶ Z}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    {N : H₀.RelHomotopy ((L.trans H₁).trans M.symm)}
    (hJ : HomotopyLift S J (N.postcomp c)) :
    SquareLift S (ParameterSquare.ofBoundary J) (N.toSquare.postcompose c) := by
  intro n r s x
  obtain ⟨z, hz⟩ := ThreeSideSquare.collapse_surjective (r, s)
  have hr := congrArg _root_.Prod.fst hz
  have hs := congrArg _root_.Prod.snd hz
  dsimp only at hr hs
  change prespectrumSimplexFamily S n (collapsed J (r, s), x) =
    c.map n (N.toSquare.level n (r, (s, x)))
  rw [← hz, collapsed_collapse]
  rw [← hr, ← hs, Homotopy.RelHomotopy.toSquare_collapse]
  exact hJ n z.1 z.2 x

end Postcomposition
end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
