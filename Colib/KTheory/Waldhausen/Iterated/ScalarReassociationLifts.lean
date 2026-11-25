/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftOperations

/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ScalarReassociationLifts.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! Whole lifts retain the actual native reassociation and constant-half contractions. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters

private theorem relative_mp_level {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K : Homotopy f g} (e : H = H')
    (p : H.RelHomotopy K = H'.RelHomotopy K) (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  rfl

private theorem relative_mp_level2 {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K K' : Homotopy f g} (eH : H = H') (eK : K = K')
    (p : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  subst K'
  rfl

/-- The continuous time change used by native reassociation of three concatenated homotopies. -/
def rectangleAssociativityTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨Path.Homotopy.transAssocReparamAux t,
    Path.Homotopy.transAssocReparamAux_mem_I t⟩, by fun_prop⟩

theorem rectangleAssociativityTime_zero : rectangleAssociativityTime 0 = 0 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_zero

theorem rectangleAssociativityTime_one : rectangleAssociativityTime 1 = 1 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_one

/-- Exact level formula for the original native associator. -/
theorem native_associativity_level {E F : LoopPrespectrum.{u}}
    {f g h k : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k) (n : ℕ) :
    ((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam (H.trans (K.trans L)) rectangleAssociativityTime
        rectangleAssociativityTime_zero
        rectangleAssociativityTime_one).symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.transAssoc
  dsimp only
  apply relative_mp_level
  apply LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have he := Path.Homotopy.trans_assoc_reparam (H.path n x) (K.path n x) (L.path n x)
  simp only [← Homotopy.path_trans] at he
  exact (DFunLike.congr_fun he s).symm

variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
  (S : ModelSimplex V W k)
  {a b c d : StdSimplex ℝ (Fin (k + 1))}
  {f g h j : prespectrum V ⟶ prespectrum W}

/-- The common-simplex scalar reassociation is precisely the old native reassociation. -/
theorem RectanglePathLift.transAssoc {p : Path a b} {q : Path b c} {z : Path c d}
    {H : Homotopy f g} {K : Homotopy g h} {L : Homotopy h j}
    (hp : PathLift S p H) (hq : PathLift S q K) (hz : PathLift S z L) :
    HomotopyLift S (Path.Homotopy.transAssoc p q z) (Homotopy.RelHomotopy.transAssoc H K L) := by
  intro n r s x
  change prespectrumSimplexFamily S n (Path.Homotopy.transAssoc p q z (r, s), x) =
    ((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap (r, (s, x))
  rw [native_associativity_level]
  exact (PathLift.trans S hp (PathLift.trans S hq hz)) n _ x

/-- The continuous time change used to remove the terminal constant segment of a native homotopy. -/
def rectangleTerminalTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨Path.Homotopy.transReflReparamAux t,
    Path.Homotopy.transReflReparamAux_mem_I t⟩, by fun_prop⟩

theorem rectangleTerminalTime_zero : rectangleTerminalTime 0 = 0 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_zero

theorem rectangleTerminalTime_one : rectangleTerminalTime 1 = 1 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_one

/-- The canonical terminal-half clock evaluates the full native relative homotopy. -/
theorem native_terminal_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam H rectangleTerminalTime
        rectangleTerminalTime_zero rectangleTerminalTime_one).symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.transRefl
  dsimp only
  apply relative_mp_level
  apply LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have he := Path.Homotopy.trans_refl_reparam (H.path n x)
  rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at he
  exact (DFunLike.congr_fun he s).symm

/-- The common-simplex scalar terminal contraction retains the native constant half. -/
theorem RectanglePathLift.transRefl {p : Path a b} {H : Homotopy f g} (hp : PathLift S p H) :
    HomotopyLift S (Path.Homotopy.transRefl p) (Homotopy.RelHomotopy.transRefl H) := by
  intro n r s x
  change prespectrumSimplexFamily S n (Path.Homotopy.transRefl p (r, s), x) =
    ((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap (r, (s, x))
  rw [native_terminal_level]
  exact hp n _ x

/-- Reversing that same clock contracts the native initial half. -/
theorem native_initial_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.reflTrans H).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.transRefl H.symm).symmPath).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.reflTrans
  apply relative_mp_level2
  · simp only [Homotopy.symm_trans, Homotopy.symm_refl, Homotopy.symm_symm]
  · exact Homotopy.symm_symm H

/-- The native initial constant half uses precisely the reversed terminal contraction. -/
theorem RectanglePathLift.reflTrans {p : Path a b} {H : Homotopy f g} (hp : PathLift S p H) :
    HomotopyLift S (Path.Homotopy.reflTrans p) (Homotopy.RelHomotopy.reflTrans H) := by
  intro n r s x
  change prespectrumSimplexFamily S n (Path.Homotopy.reflTrans p (r, s), x) =
    ((Homotopy.RelHomotopy.reflTrans H).level n).toContinuousMap (r, (s, x))
  rw [native_initial_level]
  exact (HomotopyLift.symmPath S (RectanglePathLift.transRefl S (PathLift.symm S hp))) n r s x

private theorem native_reflSymmTrans_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.reflSymmTrans H).level n).toContinuousMap =
      ((Homotopy.RelHomotopy.reflTransSymm H.symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.reflSymmTrans
  apply relative_mp_level2
  · rfl
  · rw [Homotopy.symm_symm]

/-- The reversed-then-forward cancellation has the literal native contraction parameter. -/
theorem RectanglePathLift.reflSymmTrans {p : Path a b} {H : Homotopy f g} (hp : PathLift S p H) :
    HomotopyLift S
      ((Path.Homotopy.reflTransSymm p.symm).cast rfl
        (congrArg (fun q ↦ p.symm.trans q) (Path.symm_symm p)))
      (Homotopy.RelHomotopy.reflSymmTrans H) := by
  intro n r s x
  change prespectrumSimplexFamily S n
    (Path.Homotopy.reflTransSymm p.symm (r, s), x) =
    ((Homotopy.RelHomotopy.reflSymmTrans H).level n).toContinuousMap (r, (s, x))
  rw [native_reflSymmTrans_level]
  exact (PathLift.reflTransSymm S (PathLift.symm S hp)) n r s x

end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
