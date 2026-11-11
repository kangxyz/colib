/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedSuccessor
public import Colib.KTheory.Bass.StrictDiagramSuccessorMap

/-!
# The original iterated-seed adjacent square from finite base rotations

The induction retains the original strictDiagramTransition and the unchanged stageMap.
The displayed hypothesis consists solely of local two-cone seed-rotation equations.
This conditional theorem does not assert that their geometric specialization is established.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology IteratedLoopStrength FiniteLoopWords
open AssociatedStrength NormalizedStageMap FiniteLoopWordSlide
open GeometricConeInterchange GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The initial twisted transition is exactly the original seed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedInduction.lean:34"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem twistedTransition_zero (A : Track laurent.op coefficient F) :
    twistedTransition A 0 = seed A := by
  rw [twistedTransition, normalizedTransition_loopInto, betaAt_zero_hom, loopMap_id]
  change seed A ≫ 𝟙 _ ≫ 𝟙 _ = seed A
  rw [Category.comp_id, Category.comp_id]

private theorem transition_successor_cast {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) {G : C ⥤ LoopPrespectrum.{w}}
    (a : G ⟶ (strictDiagramFunctor Q).obj G) (i : ℕ) :
    strictDiagramTransition Q a (i + 1) ≫ eqToHom (bass_succ_eq Q (i + 1) G) =
      eqToHom (bass_succ_eq Q i G) ≫
        (strictDiagramFunctor Q).map (strictDiagramTransition Q a i) :=
  strictDiagramSuccessorMap_transition Q a i

/-- The unchanged stage maps intertwine the original iterated seed and fixed twisted transitions
whenever the displayed local geometric seed rotation holds at each finite cone stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedInduction.lean:50"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem originalTransition_stageMap_of_rotation (A : Track laurent.op coefficient F)
    (hbase : ∀ i : ℕ,
      (strictDiagramFunctor squareFunctor).map (seed (coneTrack A i)) ≫
          strengthDiagram squareFunctor (iterate squareFunctor (i + 1) F) =
        Functor.whiskerRight (seed (coneTrack A (i + 1))) parameterLoopingFunctor ≫
          (transposeIso (iterate squareFunctor (i + 2) F)).inv ≫
          loopMap 2 (permutationNatIso (iterate squareFunctor i F)).hom)
    (i : ℕ) :
    strictDiagramTransition squareFunctor (seed A) i ≫ stageMap squareFunctor (i + 1) F =
      stageMap squareFunctor i F ≫ twistedTransition A i := by
  induction i with
  | zero =>
    rw [twistedTransition_zero]
    change seed A ≫ (𝟙 _ ≫ (strictDiagramFunctor squareFunctor).map (𝟙 F) ≫
      𝟙 _ ≫ 𝟙 _) = 𝟙 _ ≫ seed A
    rw [(strictDiagramFunctor squareFunctor).map_id]
    simp only [Category.id_comp, Category.comp_id]
  | succ i ih =>
    have ht := twistedTransition_successor A i (hbase i)
    have hi :
        (strictDiagramFunctor squareFunctor).map
          (strictDiagramTransition squareFunctor (seed A) i) ≫
            (strictDiagramFunctor squareFunctor).map (stageMap squareFunctor (i + 1) F) ≫
            associatedStrength squareFunctor (i + 1) (iterate squareFunctor (i + 1) F) =
          (strictDiagramFunctor squareFunctor).map (stageMap squareFunctor i F) ≫
            associatedStrength squareFunctor i (iterate squareFunctor i F) ≫
            twistedTransition A (i + 1) := by
      rw [← Category.assoc, ← (strictDiagramFunctor squareFunctor).map_comp, ih,
        (strictDiagramFunctor squareFunctor).map_comp, Category.assoc, ht]
    rw [stageMap_succ squareFunctor (i + 1) F, ← Category.assoc,
      transition_successor_cast]
    simp only [Category.assoc]
    rw [hi, stageMap_succ squareFunctor i F]
    simp only [Category.assoc]

end KTheory.Bass.SchemeIteratedSeedTransition
