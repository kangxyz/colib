/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-! # Whole relative comparisons under equality of their common-prefix index -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {ι : Type v}
  (f g : ι → (E ⟶ F)) (C : ∀ i, Homotopy (f i) (g i))
  {i j : ι} {b c : E ⟶ F}
  {D : Homotopy (g j) c} {L : Homotopy (f j) b} {M : Homotopy b c}

/-- Transport the prefix index while leaving the complete original relative family unchanged. -/
def transportPrefix (h : i = j) (J : ((C j).trans D).RelHomotopy (L.trans M)) :
    ((C i).trans (D.cast (congrArg g h).symm rfl)).RelHomotopy
      ((L.cast (congrArg f h).symm rfl).trans M) := by
  subst j
  exact J.ofLevels _ _ (fun _ => rfl) (fun _ => rfl)

/-- Index transport preserves the original entire two-parameter continuous map. -/
theorem transportPrefix_level (h : i = j)
    (J : ((C j).trans D).RelHomotopy (L.trans M)) (n : ℕ) :
    ((transportPrefix f g C h J).level n).toContinuousMap =
      (J.level n).toContinuousMap := by
  subst j
  rfl

end Topology.LoopPrespectrum.Homotopy.RelHomotopy
