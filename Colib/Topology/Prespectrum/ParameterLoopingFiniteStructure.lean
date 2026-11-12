/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ParameterLooping
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence
public import Colib.Topology.Prespectrum.FiniteStructureTransport

/-!
# Finite structure ranges under parameter-correct looping

The actual double-loop transpose is retained as a homeomorphism. Spectrum and loop
times are independent; no identification of their ordering is assumed.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/ParameterLoopingFiniteStructure.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual based maps,
finite degrees and original proof steps are retained under native names. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- The original parameter-loop structure gains its range from the next homotopy degree. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ParameterLoopingFiniteStructure.lean:25-46"
  "adaptation" "Successor-degree looping and the actual double-loop transpose preserve bijectivity"]
theorem parameterLooping_structure_bijective (E : LoopPrespectrum.{u}) (n j : ℕ)
    (hs : Function.Bijective (HomotopyGroup.map (N := Fin (j + 1))
      (E.structureMap n) (E.map_point n))) :
    Function.Bijective (HomotopyGroup.map (N := Fin j)
      ((parameterLooping E).structureMap n) ((parameterLooping E).map_point n)) := by
  have hl := HomotopyGroup.map_basedLoopMap_bijective_of_succ
    (E.structureMap n) (E.map_point n) j hs
  have ht := homotopyGroupMap_bijective_of_homotopyEquiv
    (Path.doubleLoopTransposeHomeomorph (E.point (n + 1))).toHomotopyEquiv
    (Path.doubleLoopTranspose_refl _) j
  have h := ht.comp hl
  have hw : HomotopyGroup.map (N := Fin j)
      ((parameterLooping E).structureMap n) ((parameterLooping E).map_point n) =
    HomotopyGroup.map (N := Fin j) (Path.doubleLoopTranspose (E.point (n + 1)))
      (Path.doubleLoopTranspose_refl _) ∘
    HomotopyGroup.map (N := Fin j) (basedLoopMap (E.structureMap n) (E.map_point n))
      (basedLoopMap_refl _ _) := by
    funext z
    exact HomotopyGroup.map_comp _ (basedLoopMap_refl _ _)
      _ (Path.doubleLoopTranspose_refl _) z
  rw [hw]
  exact h

end Topology.LoopPrespectrum
