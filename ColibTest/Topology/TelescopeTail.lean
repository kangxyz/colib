/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.Topology.Prespectrum.TelescopeTail
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.LoopPrespectrum.Telescope.TailTest
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

example (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    (toTail E f).map k (cylinder E f k i (s, x)) =
      cylinder (fun i => E (i + 1)) (fun i => f (i + 1)) k i (s, (f i).map k x) :=
  toTail_cylinder E f k i s x

example (i : ℕ) :
    inclusion (fun i => E (i + 1)) (fun i => f (i + 1)) i ≫ tailInclusion E f =
      inclusion E f (i + 1) :=
  inclusion_tailInclusion E f i

variable [∀ i k, T1Space ((E i).space k)]

example {F : LoopPrespectrum.{u}} (a b : prespectrum E f ⟶ F) (d : ℤ)
    (h : ∀ i, (stableHomotopyFunctor d).map (inclusion E f i ≫ a) =
      (stableHomotopyFunctor d).map (inclusion E f i ≫ b)) :
    (stableHomotopyFunctor d).map a = (stableHomotopyFunctor d).map b :=
  stableMap_ext E f a b d h

example : IsStableEquivalence (tailInclusion E f) :=
  tailInclusion_isStableEquivalence E f

end Topology.LoopPrespectrum.Telescope.TailTest
