/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# Exact pointwise evaluation of the original relative associator

The existing transAssoc equality transport is retained. Only after projecting the whole
level is its endpoint equality proved using the original path reparameterization theorem.
Every level, input point and both independent times are retained.

Adapted from `Quillen/Topology/Prespectrum/RelativeHomotopyAssociatorEvaluation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
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

private def associatorTime : C(unitInterval, unitInterval) :=
  ⟨fun s ↦ ⟨Path.Homotopy.transAssocReparamAux s,
    Path.Homotopy.transAssocReparamAux_mem_I s⟩, by fun_prop⟩

private theorem associatorTime_zero : associatorTime 0 = 0 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_zero

private theorem associatorTime_one : associatorTime 1 = 1 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_one

private theorem associator_level {E F : LoopPrespectrum.{u}}
    {f g h k : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h)
    (L : Homotopy h k) (n : ℕ) :
    ((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam (H.trans (K.trans L)) associatorTime
        associatorTime_zero associatorTime_one).symm).level n).toContinuousMap := by
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

/-- The original relative associator evaluates to the literal scalar associator at every point. -/
theorem Homotopy.RelHomotopy.transAssoc_apply_path {E F : LoopPrespectrum.{u}}
    {f g h k : E ⟶ F} (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x)) =
      Path.Homotopy.transAssoc (H.path n x) (K.path n x) (L.path n x) (r, s) := by
  change ((Homotopy.RelHomotopy.transAssoc H K L).level n).toContinuousMap (r, (s, x)) = _
  rw [associator_level]
  change (H.trans (K.trans L)).path n x _ =
    ((H.path n x).trans ((K.path n x).trans (L.path n x))) _
  rw [Homotopy.path_trans, Homotopy.path_trans]
  exact congrArg (fun t : unitInterval ↦
    ((H.path n x).trans ((K.path n x).trans (L.path n x))) t)
    (Subtype.ext (by rfl))

end Topology.LoopPrespectrum
