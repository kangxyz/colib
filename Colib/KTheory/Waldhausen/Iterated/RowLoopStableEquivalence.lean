/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.RowLoopPrespectrum
public import Colib.KTheory.Waldhausen.Iterated.OmegaSpectrum
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.WeakEquivalence
public import Colib.Topology.Prespectrum.StableEquivalence

/-!
# Stability of the actual distinguished-row comparison

The positive comparison levels are the unchanged original S-structure maps, whose complete
weak equivalence is already proved. Degree zero is their actual based-loop extension. Thus the
whole row-stabilization map is levelwise weak and induces isomorphisms in every stable degree.
No point-set inverse or equality with ordinary loop-tail stabilization is introduced.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/RowLoopStableEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
row transpose, based maps, independent time coordinates and hypotheses are retained.
The existing native wide category of zero-preserving exact maps supplies the original models. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- Every actual row-stabilization level is a complete weak equivalence. -/
theorem rowStabilizationMap_weak (W : WideSubcategory preservesZero.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((rowStabilizationMap W).map n) := by
  cases n with
  | zero =>
    exact basedLoopMap_isWeakHomotopyEquivalence (stageLoopMap 0 W)
      (stageLoopMap_point 0 W) (stageLoopMap_weak 0 W)
  | succ k => exact stageLoopMap_weak k W

/-- The original actual row-stabilization map is stable in every integer degree. -/
theorem rowStabilizationMap_isStableEquivalence (W : WideSubcategory preservesZero.{u}) :
    LoopPrespectrum.IsStableEquivalence (rowStabilizationMap W) :=
  LoopPrespectrum.isStableEquivalence_of_levelwise _ (rowStabilizationMap_weak W)

attribute [colib_tag "COL-0293"] rowStabilizationMap_weak
  rowStabilizationMap_isStableEquivalence

attribute [colib_ref "Waldhausen1985"
  "Section 1.5, Proposition 1.5.3 and following paragraph, p. 342" "ingredient"
  "The iterated S-loop equivalences underlie the actual distinguished-row comparison;
    its row transpose and zero-level double loop are retained here"]
  rowStabilizationMap_weak rowStabilizationMap_isStableEquivalence

end CategoryTheory.Waldhausen.IteratedS
