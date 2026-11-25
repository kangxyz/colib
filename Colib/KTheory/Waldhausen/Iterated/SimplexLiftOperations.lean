/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexParameterPaths
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting

/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/SimplexLiftOperations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! Exact parameter lifts for the old prespectrum track operations and three-side collapse. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  {k : ℕ} (S : ModelSimplex V W k)
  {a b c : StdSimplex ℝ (Fin (k + 1))}
  {f g h : prespectrum V ⟶ prespectrum W}

/-- Pointwise equality with the specified whole native track, with its endpoints left unchanged. -/
def PathLift (p : Path a b) (H : Homotopy f g) : Prop :=
  ∀ n t x, prespectrumSimplexFamily S n (p t, x) = H.level n (t, x)

/-- Pointwise equality with a specified whole native relative comparison. -/
def HomotopyLift {p q : Path a b} (J : p.Homotopy q)
    {H K : Homotopy f g} (M : H.RelHomotopy K) : Prop :=
  ∀ n r s x, prespectrumSimplexFamily S n (J (r, s), x) = M.level n (r, (s, x))

theorem HomotopyLift.source {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M) :
    PathLift S p H := by
  intro n t x
  calc
    prespectrumSimplexFamily S n (p t, x) =
        prespectrumSimplexFamily S n (J (0, t), x) := by rw [J.apply_zero]; rfl
    _ = M.level n (0, (t, x)) := hJ n 0 t x
    _ = H.level n (t, x) := (M.level n).apply_zero _

theorem HomotopyLift.target {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M) :
    PathLift S q K := by
  intro n t x
  calc
    prespectrumSimplexFamily S n (q t, x) =
        prespectrumSimplexFamily S n (J (1, t), x) := by rw [J.apply_one]; rfl
    _ = M.level n (1, (t, x)) := hJ n 1 t x
    _ = K.level n (t, x) := (M.level n).apply_one _

theorem PathLift.refl {p : Path a b} {H : Homotopy f g} (hp : PathLift S p H) :
    HomotopyLift S (Path.Homotopy.refl p) (Homotopy.RelHomotopy.refl H) := by
  intro n r s x
  exact hp n s x

/-- Whole-level endpoint transport in the existing API changes no scalar lift. -/
theorem HomotopyLift.ofLevels {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M)
    {f' g' : prespectrum V ⟶ prespectrum W} (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n) :
    HomotopyLift S J (Homotopy.RelHomotopy.ofLevels M H' K' hH hK) := hJ

theorem PathLift.symm {p : Path a b} {H : Homotopy f g} (hp : PathLift S p H) :
    PathLift S p.symm H.symm := by
  intro n t x
  exact hp n (unitInterval.symm t) x

theorem PathLift.trans {p : Path a b} {q : Path b c}
    {H : Homotopy f g} {K : Homotopy g h} (hp : PathLift S p H) (hq : PathLift S q K) :
    PathLift S (p.trans q) (H.trans K) := by
  intro n t x
  change prespectrumSimplexFamily S n ((p.trans q) t, x) =
    ((H.levelHomotopy n).trans (K.levelHomotopy n)) (t, x)
  rw [Path.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> first | exact hp n _ x | exact hq n _ x

theorem HomotopyLift.symm {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M) :
    HomotopyLift S J.symm M.symm := by
  intro n r s x
  exact hJ n (unitInterval.symm r) s x

theorem HomotopyLift.symmPath {p q : Path a b} {J : p.Homotopy q}
    {H K : Homotopy f g} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M) :
    HomotopyLift S J.symm₂ M.symmPath := by
  intro n r s x
  exact hJ n r (unitInterval.symm s) x

theorem HomotopyLift.trans {p q z : Path a b} {J : p.Homotopy q} {K : q.Homotopy z}
    {H H' H'' : Homotopy f g} {M : H.RelHomotopy H'} {N : H'.RelHomotopy H''}
    (hJ : HomotopyLift S J M) (hK : HomotopyLift S K N) :
    HomotopyLift S (J.trans K) (M.trans N) := by
  intro n r s x
  change prespectrumSimplexFamily S n ((J.trans K) (r, s), x) =
    ((M.level n).trans (N.level n)) (r, (s, x))
  rw [Path.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> first | exact hJ n _ s x | exact hK n _ s x

private theorem relative_hcomp_apply {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K') (n : ℕ) (r s : unitInterval)
    (x : (prespectrum V).space n) :
    (J.hcomp L).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n
          (r, (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else L.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

theorem HomotopyLift.hcomp {p q : Path a b} {p' q' : Path b c}
    {J : p.Homotopy q} {K : p'.Homotopy q'}
    {H H' : Homotopy f g} {L L' : Homotopy g h}
    {M : H.RelHomotopy H'} {N : L.RelHomotopy L'}
    (hJ : HomotopyLift S J M) (hK : HomotopyLift S K N) :
    HomotopyLift S (J.hcomp K) (M.hcomp N) := by
  intro n r s x
  rw [Path.Homotopy.hcomp_apply, relative_hcomp_apply]
  split <;> first | exact hJ n r _ x | exact hK n r _ x

/-- The native linear reparameterization comparison keeps its exact scalar parameter formula. -/
theorem PathLift.reparam {p : Path a b} {H : Homotopy f g} (hp : PathLift S p H)
    (φ : C(unitInterval, unitInterval)) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    HomotopyLift S (Path.Homotopy.reparam p φ φ.continuous h0 h1)
      (Homotopy.RelHomotopy.reparam H φ h0 h1) := by
  intro n r s x
  exact hp n _ x

/-- The native cancellation comparison keeps its exact old contraction parameter. -/
theorem PathLift.reflTransSymm {p : Path a b} {H : Homotopy f g}
    (hp : PathLift S p H) :
    HomotopyLift S (Path.Homotopy.reflTransSymm p) (Homotopy.RelHomotopy.reflTransSymm H) := by
  intro n r s x
  exact hp n _ x

/-- Descend the scalar surface through the same actual three-side quotient used by native Bass. -/
def collapsed {p q : Path a b} (J : p.Homotopy q) :
    C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  let A : C((unitInterval × unitInterval) × Unit, StdSimplex ℝ (Fin (k + 1))) :=
    ⟨fun z ↦ J z.1, by fun_prop⟩
  let h0 : ∀ r x, A ((r, 0), x) = A ((0, 0), x) :=
    fun r _ ↦ (J.source r).trans (J.source 0).symm
  let h1 : ∀ r x, A ((r, 1), x) = A ((0, 1), x) :=
    fun r _ ↦ (J.target r).trans (J.target 0).symm
  ⟨fun z ↦ ThreeSideSquare.liftFamily A h0 h1 (z, ()), by fun_prop⟩

theorem collapsed_collapse {p q : Path a b} (J : p.Homotopy q)
    (z : unitInterval × unitInterval) : collapsed J (ThreeSideSquare.collapse z) = J z :=
  ThreeSideSquare.liftFamily_collapse
    (⟨fun z : (unitInterval × unitInterval) × Unit ↦ J z.1, by fun_prop⟩ :
      C((unitInterval × unitInterval) × Unit, StdSimplex ℝ (Fin (k + 1))))
    (fun r _ ↦ (J.source r).trans (J.source 0).symm)
    (fun r _ ↦ (J.target r).trans (J.target 0).symm) z ()

/-- An exact whole lift survives the native three-side collapse pointwise, not only at edges. -/
theorem HomotopyLift.toSquare {p q : Path a b} {J : p.Homotopy q}
    {a₀ b₀ a₁ b₁ : prespectrum V ⟶ prespectrum W}
    {H₀ : Homotopy a₀ b₀} {H₁ : Homotopy a₁ b₁}
    {L : Homotopy a₀ a₁} {M : Homotopy b₀ b₁}
    {N : H₀.RelHomotopy ((L.trans H₁).trans M.symm)} (hJ : HomotopyLift S J N)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (collapsed J (r, s), x) =
      N.toSquare.level n (r, (s, x)) := by
  obtain ⟨z, hz⟩ := ThreeSideSquare.collapse_surjective (r, s)
  have hr := congrArg _root_.Prod.fst hz
  have hs := congrArg _root_.Prod.snd hz
  dsimp only at hr hs
  rw [← hz, collapsed_collapse]
  change prespectrumSimplexFamily S n (J z, x) = N.toSquare.level n (r, (s, x))
  rw [← hr, ← hs, Homotopy.RelHomotopy.toSquare_collapse]
  exact hJ n z.1 z.2 x

end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
