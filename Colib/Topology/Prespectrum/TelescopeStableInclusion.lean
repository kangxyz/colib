/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.EventuallyIsoColimit
public import Colib.Topology.Prespectrum.TelescopeStableColimit

/-!
# Original stable telescope inclusions after stabilization

For levelwise T1 prespectra, invertibility of the original transitions in one
fixed degree from stage `i` onward implies invertibility of the actual stage
`i` telescope inclusion in that degree. Earlier stages need not be stable.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  [∀ i k, T1Space ((E i).space k)]

/-- Stabilization beginning at `i` makes the original inclusion at `i` invertible. -/
theorem inclusion_stableMap_isIso_of_tail (d : ℤ) (i : ℕ)
    (h : ∀ n, i ≤ n → IsIso ((stableHomotopyFunctor d).map (f n))) :
    IsIso ((stableHomotopyFunctor d).map (inclusion E f i)) := by
  have hi : IsIso (colimit.ι (stageStableDiagram E f d) i) :=
    CategoryTheory.Limits.SequentialSystem.colimit_ι_isIso_of_tail _ i (by
      intro n hn
      simpa only [stageStableDiagram, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ] using h n hn)
  rw [← stableColimitIso_ι_hom E f d i]
  exact IsIso.comp_isIso' hi (stableColimitIso E f d).isIso_hom

end Topology.LoopPrespectrum.Telescope
