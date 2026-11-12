/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.ModelDiagramRowComparison
public import Colib.KTheory.Bass.ModelDiagramConeFiniteStructure
public import Colib.Topology.Prespectrum.StableFiniteRange
public import Colib.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-! # Stability of the actual finite-stage row comparison

The original finite-range proof applies to the unchanged native construction.
-/
/-! Implementation provenance:
`Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- No positive component of the original structure comparison has been changed. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:47"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem comparison_succ (X : C) (k : ℕ) :
    (comparison Q i F X).map (k + 1) = (source Q i F X).structureMap (k + 1) := rfl

/-- Degree zero retains both original structure maps and their independent parameters. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:51"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem comparison_zero (X : C) (x : (source Q i F X).space 0) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((comparison Q i F X).map 0 x) r) s =
      (source Q i F X).structureMap 1 ((source Q i F X).structureMap 0 x r) s := rfl

/-- The finite-stage comparison is stable using its actual target structure and finite range. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:56"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem comparison_isStableEquivalence (X : C) :
    IsStableEquivalence (comparison Q i F X) := by
  apply isStableEquivalence_of_eventually_linearPi (comparison Q i F X) (i + 2) (2 * i + 2)
  intro n hn k hk
  change Function.Bijective (HomotopyGroup.map (N := Fin (k + 2))
    ((source Q i F X).structureMap (n + 1)) ((source Q i F X).map_point (n + 1)))
  have h := modelDiagramIterate_cone_structure_bijective Q i F X (n - (i + 2)) k (by omega)
  rw [show n - (i + 2) + i + 3 = n + 1 by omega] at h
  exact h

/-- Actual parameter looping preserves this stable roof at every finite stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowRefinement.lean:67"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem parameterComparison_isStableEquivalence (X : C) :
    IsStableEquivalence (parameterLoopingMap (comparison Q i F X)) :=
  parameterLoopingMap_isStableEquivalence _ (comparison_isStableEquivalence Q i F X)

end KTheory.Bass.ModelDiagramRowRefinement
