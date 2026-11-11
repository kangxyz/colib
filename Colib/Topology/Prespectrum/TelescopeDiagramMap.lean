/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeDiagram

/-!
# Original telescope maps of strict sequences of diagrams

A strict stagewise natural arrow preserving the original transitions induces the actual
quotient telescope map. Its cylinder height and stage inclusion are unchanged, and
coefficient naturality is proved on every original cylinder.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u v w
namespace Topology.LoopPrespectrum.Telescope
variable {C : Type u} [Category.{v} C]
    (F G : ℕ → C ⥤ LoopPrespectrum.{w})
    (τ : ∀ i, F i ⟶ F (i + 1)) (σ : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, F i ⟶ G i) (h : ∀ i, a i ≫ σ i = τ i ≫ a (i + 1))

/-- The same original strict stage maps act on the entire quotient telescope diagram. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeDiagramMap.lean:28"
  "adaptation" "Original strict diagram telescope map and complete cylinder naturality."]
def diagramMap : diagramFunctor F τ ⟶ diagramFunctor G σ where
  app X := map (fun i ↦ (F i).obj X) (fun i ↦ (τ i).app X)
    (fun i ↦ (G i).obj X) (fun i ↦ (σ i).app X) (fun i ↦ (a i).app X)
    (fun i ↦ congrArg (fun t ↦ t.app X) (h i))
  naturality X Y f := by
    apply hom_ext
    intro k i s x
    change cylinder (fun j ↦ (G j).obj Y) (fun j ↦ (σ j).app Y) k i
        (s, ((a i).app Y).map k (((F i).map f).map k x)) =
      cylinder (fun j ↦ (G j).obj Y) (fun j ↦ (σ j).app Y) k i
        (s, ((G i).map f).map k (((a i).app X).map k x))
    exact congrArg (fun y ↦ cylinder (fun j ↦ (G j).obj Y)
      (fun j ↦ (σ j).app Y) k i (s, y))
      (congrArg (fun t ↦ t.map k x) ((a i).naturality f))

/-- No telescope height or original stage map is changed by this natural transformation. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeDiagramMap.lean:44"
  "adaptation" "Original strict diagram telescope map and complete cylinder naturality."]
theorem diagramMap_cylinder (X : C) (k i : ℕ) (s : unitInterval)
    (x : ((F i).obj X).space k) :
    ((diagramMap F G τ σ a h).app X).map k
        (cylinder (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) k i (s, x)) =
      cylinder (fun j ↦ (G j).obj X) (fun j ↦ (σ j).app X) k i
        (s, ((a i).app X).map k x) := rfl

/-- The actual stage inclusion commutes with the original induced telescope map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeDiagramMap.lean:52"
  "adaptation" "Original strict diagram telescope map and complete cylinder naturality."]
theorem diagramInclusion_diagramMap (i : ℕ) :
    diagramInclusion F τ i ≫ diagramMap F G τ σ a h = a i ≫ diagramInclusion G σ i := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext k
  apply ContinuousMap.ext
  intro x
  rfl

end Topology.LoopPrespectrum.Telescope
