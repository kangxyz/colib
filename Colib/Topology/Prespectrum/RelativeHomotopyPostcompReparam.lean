/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyPostcompLevels

/-! Postcomposition retains the actual original associator and cancellation families,
including their proposition-level endpoint transports and unchanged time functions. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

private theorem transport_level {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K K' : Homotopy f g} (eH : H = H') (eK : K = K')
    (p : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  subst K'
  rfl

private def associativityTime : C(unitInterval, unitInterval) :=
  ⟨fun s ↦ ⟨Path.Homotopy.transAssocReparamAux s,
    Path.Homotopy.transAssocReparamAux_mem_I s⟩, by fun_prop⟩

private theorem associativityTime_zero : associativityTime 0 = 0 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_zero

private theorem associativityTime_one : associativityTime 1 = 1 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_one

private theorem associativity_level {E F : LoopPrespectrum.{u}}
    {f g h k : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k) (n : ℕ) :
    ((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam (H.trans (K.trans L)) associativityTime
        associativityTime_zero associativityTime_one).symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.transAssoc
  dsimp only
  apply transport_level
  · apply Homotopy.ext
    funext n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    have he := Path.Homotopy.trans_assoc_reparam (H.path n x) (K.path n x) (L.path n x)
    simp only [← Homotopy.path_trans] at he
    exact (DFunLike.congr_fun he s).symm
  · rfl

private def terminalTime : C(unitInterval, unitInterval) :=
  ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s,
    Path.Homotopy.transReflReparamAux_mem_I s⟩, by fun_prop⟩

private theorem terminalTime_zero : terminalTime 0 = 0 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_zero

private theorem terminalTime_one : terminalTime 1 = 1 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_one

private theorem terminal_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam H terminalTime
        terminalTime_zero terminalTime_one).symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.transRefl
  dsimp only
  apply transport_level
  · apply Homotopy.ext
    funext n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    have he := Path.Homotopy.trans_refl_reparam (H.path n x)
    rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at he
    exact (DFunLike.congr_fun he s).symm
  · rfl

private theorem initial_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.reflTrans H).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.transRefl H.symm).symmPath).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.reflTrans
  apply transport_level
  · simp only [Homotopy.symm_trans, Homotopy.symm_refl, Homotopy.symm_symm]
  · exact Homotopy.symm_symm H

private theorem reverseCancellation_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.reflSymmTrans H).level n).toContinuousMap =
      ((Homotopy.RelHomotopy.reflTransSymm H.symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.reflSymmTrans
  apply transport_level
  · rfl
  · simp only [Homotopy.symm_symm]

namespace Homotopy.MappedAt
variable {E F G : LoopPrespectrum.{u}} {j : F ⟶ G} {n : ℕ} {x : E.space n}
  {f g h k : E ⟶ F} {f' g' h' k' : E ⟶ G}
  {H : Homotopy f g} {H' : Homotopy f' g'}

/-- The original dyadic associator commutes pointwise with the supplied target map. -/
theorem transAssoc {K : Homotopy g h} {K' : Homotopy g' h'}
    {L : Homotopy h k} {L' : Homotopy h' k'}
    (hH : H.MappedAt j n x H') (hK : K.MappedAt j n x K')
    (hL : L.MappedAt j n x L') :
    (Homotopy.RelHomotopy.transAssoc H K L).MappedAt j n x
      (Homotopy.RelHomotopy.transAssoc H' K' L') := by
  intro r s
  change j.map n (((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap
    (r, (s, x))) =
    ((Homotopy.RelHomotopy.transAssoc H' K' L').level n).toContinuousMap (r, (s, x))
  rw [associativity_level, associativity_level]
  exact (hH.trans (hK.trans hL)) _

/-- Removing the terminal constant half retains the original interpolation. -/
theorem transRefl (hH : H.MappedAt j n x H') :
    (Homotopy.RelHomotopy.transRefl H).MappedAt j n x
      (Homotopy.RelHomotopy.transRefl H') := by
  intro r s
  change j.map n (((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap
    (r, (s, x))) =
    ((Homotopy.RelHomotopy.transRefl H').level n).toContinuousMap (r, (s, x))
  rw [terminal_level, terminal_level]
  exact hH _

/-- Removing the initial constant half retains the actual reversed terminal interpolation. -/
theorem reflTrans (hH : H.MappedAt j n x H') :
    (Homotopy.RelHomotopy.reflTrans H).MappedAt j n x
      (Homotopy.RelHomotopy.reflTrans H') := by
  intro r s
  change j.map n (((Homotopy.RelHomotopy.reflTrans H).level n).toContinuousMap
    (r, (s, x))) =
    ((Homotopy.RelHomotopy.reflTrans H').level n).toContinuousMap (r, (s, x))
  rw [initial_level, initial_level]
  exact hH.symm.transRefl.symmPath r s

/-- Actual forward-then-reverse cancellation retains the same two-coordinate family. -/
theorem reflTransSymm (hH : H.MappedAt j n x H') :
    (Homotopy.RelHomotopy.reflTransSymm H).MappedAt j n x
      (Homotopy.RelHomotopy.reflTransSymm H') := by
  intro r s
  exact hH _

/-- Actual reverse-then-forward cancellation retains the same two-coordinate family. -/
theorem reflSymmTrans (hH : H.MappedAt j n x H') :
    (Homotopy.RelHomotopy.reflSymmTrans H).MappedAt j n x
      (Homotopy.RelHomotopy.reflSymmTrans H') := by
  intro r s
  change j.map n (((Homotopy.RelHomotopy.reflSymmTrans H).level n).toContinuousMap
    (r, (s, x))) =
    ((Homotopy.RelHomotopy.reflSymmTrans H').level n).toContinuousMap (r, (s, x))
  rw [reverseCancellation_level, reverseCancellation_level]
  exact hH.symm.reflTransSymm r s

end Homotopy.MappedAt
end Topology.LoopPrespectrum
