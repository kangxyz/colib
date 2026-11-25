/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyConjugation

/-!
# The two equality transports needed by literal conjugation

Reverse cancellation retains the original symm_symm transport. The source retyping helper
uses exactly the symm_trans rewrite occurring in original conjugateNaturality. Its application
lemma concerns that transport alone; a complete conjugateNaturality compatibility theorem
is a separate obligation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy

/-- The actual forward-then-reversed contraction has the original scalar interior. -/
theorem reflTransSymm_apply_path {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (r s : I) (x : E.space n) :
    (reflTransSymm H).level n (r, (s, x)) =
      Path.Homotopy.reflTransSymm (H.path n x) (r, s) := rfl

private theorem reverseCancellation_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (r s : I) (x : E.space n) :
    (reflSymmTrans H).level n (r, (s, x)) =
      (reflTransSymm H.symm).level n (r, (s, x)) := by
  unfold reflSymmTrans
  apply transport_apply
  · rfl
  · simp only [Homotopy.symm_symm]

/-- Original reverse cancellation has the scalar reversed-path contraction at every point. -/
theorem reflSymmTrans_apply_path {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (r s : I) (x : E.space n) :
    (reflSymmTrans H).level n (r, (s, x)) =
      Path.Homotopy.reflTransSymm (H.path n x).symm (r, s) := by
  rw [reverseCancellation_apply, reflTransSymm_apply_path, Homotopy.path_symm]

/-- The exact source rewrite used in conjugation, with the full comparison retained. -/
def retypeSymmTransSource {E F : LoopPrespectrum.{u}} {a b c d : E ⟶ F}
    (H : Homotopy a b) (K : Homotopy b c) (W : Homotopy a d) (Z : Homotopy c d)
    (J : ((K.symm.trans H.symm).trans W).RelHomotopy Z) :
    ((H.trans K).symm.trans W).RelHomotopy Z := by
  rw [Homotopy.symm_trans]
  exact J

/-- The original symm_trans source rewrite changes neither independent time coordinate. -/
theorem retypeSymmTransSource_apply {E F : LoopPrespectrum.{u}} {a b c d : E ⟶ F}
    (H : Homotopy a b) (K : Homotopy b c) (W : Homotopy a d) (Z : Homotopy c d)
    (J : ((K.symm.trans H.symm).trans W).RelHomotopy Z)
    (n : ℕ) (r s : I) (x : E.space n) :
    (retypeSymmTransSource H K W Z J).level n (r, (s, x)) =
      J.level n (r, (s, x)) := by
  unfold retypeSymmTransSource
  apply transport_apply
  · simp only [Homotopy.symm_trans]
  · rfl

end Topology.LoopPrespectrum.Homotopy.RelHomotopy
