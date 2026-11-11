/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.AssociatedStrength

/-! # Naturality of the original finite normalized stage maps

The finite cone map is induced by the original cone functor at every stage.
The normalization maps commute with arbitrary diagram maps, retaining both
of their prescribed association casts.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.NormalizedStageMap
open FiniteConeTopology FiniteLoopWords AssociatedStrength
variable {C : Type u} [Category.{v} C]

/-- Apply the original cone map at each of the fixed finite cone stages. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageNaturality.lean:28"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def iterateMap (Q : C ⥤ Arrow (Arrow C)) : ∀ i,
    {F G : C ⥤ LoopPrespectrum.{w}} → (F ⟶ G) → (iterate Q i F ⟶ iterate Q i G)
  | 0, _, _, η => η
  | i + 1, _, _, η => ConeTrack.map Q (iterateMap Q i η)

/-- The normalized map uses exactly the original finite loops of the finite cone map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageNaturality.lean:34"
  "adaptation" "Original strength evaluation, naturality and full casts."]
def normalizedMap (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    {F G : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    normalized Q i F ⟶ normalized Q i G := loopMap i (iterateMap Q i η)

/-- The full Bass association equality is natural in the original input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageNaturality.lean:39"
  "adaptation" "Original strength evaluation, naturality and full casts.", reassoc]
theorem bass_succ_naturality (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    {F G : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    (strictDiagramIterate Q (i + 1)).map η ≫ eqToHom (bass_succ_eq Q i G) =
      eqToHom (bass_succ_eq Q i F) ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map η) := by
  induction i generalizing F G with
  | zero => simp only [eqToHom_refl, Category.comp_id, Category.id_comp]; rfl
  | succ i ih => exact ih ((strictDiagramFunctor Q).map η)

/-- Every unchanged finite stage map is natural in arbitrary diagram maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageNaturality.lean:49"
  "adaptation" "Original strength evaluation, naturality and full casts.", reassoc]
theorem stageMap_naturality (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    {F G : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    (strictDiagramIterate Q i).map η ≫ stageMap Q i G =
      stageMap Q i F ≫ normalizedMap Q i η := by
  induction i with
  | zero => exact Category.comp_id η |>.trans (Category.id_comp η).symm
  | succ i ih =>
    rw [stageMap_succ, stageMap_succ, ← Category.assoc, bass_succ_naturality]
    simp only [Category.assoc]
    apply congrArg (fun k => eqToHom (bass_succ_eq Q i F) ≫ k)
    dsimp only [normalized] at *
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ih,
      CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg (fun k => (strictDiagramFunctor Q).map (stageMap Q i F) ≫ k)
      (associatedStrength_naturality Q i (iterateMap Q i η))

end KTheory.Bass.NormalizedStageMap
