/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopySourceTransport

/-! Constructor equations keep named actual tracks opaque in whole-level pasting. -/
@[expose] public noncomputable section
open CategoryTheory
universe u

namespace Topology.LoopPrespectrum

/-- Glue supplied whole-level comparisons after separately proved constructor equations.
No endpoint-arrow equality between the two presentations is required. -/
theorem Homotopy.trans_level_congr_objects_of_eq
    {D D' E E' : LoopPrespectrum.{u}} (eD : D = D') (eE : E = E')
    {a b c : D ⟶ E} {a' b' c' : D' ⟶ E'}
    (L : Homotopy a c) (H : Homotopy a b) (K : Homotopy b c)
    (L' : Homotopy a' c') (H' : Homotopy a' b') (K' : Homotopy b' c')
    (eL : L = H.trans K) (eL' : L' = H'.trans K') (n : ℕ)
    (hH : HEq (H.level n) (H'.level n))
    (hK : HEq (K.level n) (K'.level n)) :
    HEq (L.level n) (L'.level n) := by
  subst L
  subst L'
  exact Homotopy.trans_level_congr_objects eD eE H K H' K' n hH hK

end Topology.LoopPrespectrum
