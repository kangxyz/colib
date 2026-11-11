/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.HomotopyNamedLevels
public import Colib.Topology.Prespectrum.HomotopyTransport

/-! Named concatenations retain their actual outer source and target casts. -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Compare whole levels without unfolding the named track or changing either actual
endpoint cast. The two supplied subtrack certificates retain all times. -/
theorem Homotopy.trans_cast_level_congr_objects_of_eq
    {D D' E E' : LoopPrespectrum.{u}} (eD : D = D') (eE : E = E')
    {a b c a₀ c₀ : D ⟶ E} {a' b' c' : D' ⟶ E'}
    (L : Homotopy a₀ c₀) (H : Homotopy a b) (K : Homotopy b c)
    (ha : a = a₀) (hc : c = c₀)
    (L' : Homotopy a' c') (H' : Homotopy a' b') (K' : Homotopy b' c')
    (eL : L = (H.trans K).cast ha hc) (eL' : L' = H'.trans K') (n : ℕ)
    (hH : HEq (H.level n) (H'.level n))
    (hK : HEq (K.level n) (K'.level n)) :
    HEq (L.level n) (L'.level n) := by
  subst L
  subst L'
  exact (heq_of_eq (Homotopy.cast_level (H.trans K) ha hc n)).trans
    (Homotopy.trans_level_congr_objects eD eE H K H' K' n hH hK)

end Topology.LoopPrespectrum
