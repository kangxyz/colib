/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Telescope

/-!
# The actual telescope of a strict sequence of prespectrum diagrams

The existing reduced quotient telescope is strictly functorial in coefficients when all stage
maps are. Every stage inclusion is a natural transformation, and its original cylinder gives
the actual homotopy to the next inclusion after the unchanged connecting map.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Topology.LoopPrespectrum.Telescope
variable {C : Type u} [Category.{v} C]
  (F : ℕ → C ⥤ LoopPrespectrum.{w}) (τ : ∀ i, F i ⟶ F (i + 1))

/-- Apply the original reduced telescope to the actual stage objects and connecting maps. -/
def diagramFunctor : C ⥤ LoopPrespectrum.{w} where
  obj X := prespectrum (fun i ↦ (F i).obj X) (fun i ↦ (τ i).app X)
  map {X Y} f := map (fun i ↦ (F i).obj X) (fun i ↦ (τ i).app X)
    (fun i ↦ (F i).obj Y) (fun i ↦ (τ i).app Y) (fun i ↦ (F i).map f)
    (fun i ↦ (τ i).naturality f)
  map_id X := by
    apply hom_ext
    intro k i s x
    change cylinder (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) k i
      (s, ((F i).map (𝟙 X)).map k x) =
      cylinder (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) k i (s, x)
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply hom_ext
    intro k i s x
    change cylinder (fun j ↦ (F j).obj Z) (fun j ↦ (τ j).app Z) k i
      (s, ((F i).map (f ≫ g)).map k x) =
      cylinder (fun j ↦ (F j).obj Z) (fun j ↦ (τ j).app Z) k i
        (s, ((F i).map g).map k (((F i).map f).map k x))
    rw [Functor.map_comp]
    rfl

/-- Every coefficient map retains the full original stage and cylinder coordinate. -/
theorem diagramFunctor_map_cylinder {X Y : C} (f : X ⟶ Y) (k i : ℕ) (s : unitInterval)
    (x : ((F i).obj X).space k) :
    ((diagramFunctor F τ).map f).map k
        (cylinder (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) k i (s, x)) =
      cylinder (fun j ↦ (F j).obj Y) (fun j ↦ (τ j).app Y) k i (s, ((F i).map f).map k x) := rfl

/-- The actual initial face of each stage cylinder is strictly coefficient-natural. -/
def diagramInclusion (i : ℕ) : F i ⟶ diagramFunctor F τ where
  app X := inclusion (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) i
  naturality X Y f := (inclusion_map (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X)
    (fun j ↦ (F j).obj Y) (fun j ↦ (τ j).app Y) (fun j ↦ (F j).map f)
    (fun j ↦ (τ j).naturality f) i).symm

/-- The original stage cylinder compares consecutive inclusions through the actual transition. -/
def diagramInclusionHomotopy (X : C) (i : ℕ) :
    Homotopy ((diagramInclusion F τ i).app X)
      ((τ i).app X ≫ (diagramInclusion F τ (i + 1)).app X) :=
  inclusionHomotopy (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) i

/-- The homotopy uses the whole original quotient cylinder, without reparameterization. -/
theorem diagramInclusionHomotopy_apply (X : C) (i k : ℕ) (s : unitInterval)
    (x : ((F i).obj X).space k) :
    (diagramInclusionHomotopy F τ X i).level k (s, x) =
      cylinder (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) k i (s, x) := rfl

/-- Coefficients commute with the literal inclusion homotopy at the same cylinder time. -/
theorem diagramInclusionHomotopy_naturality_apply {X Y : C} (f : X ⟶ Y)
    (i k : ℕ) (s : unitInterval) (x : ((F i).obj X).space k) :
    ((diagramFunctor F τ).map f).map k
        ((diagramInclusionHomotopy F τ X i).level k (s, x)) =
      (diagramInclusionHomotopy F τ Y i).level k (s, ((F i).map f).map k x) := rfl

end Topology.LoopPrespectrum.Telescope

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeDiagram.lean:25-47"
  "adaptation" "Strict coefficient functor on the actual reduced quotient telescope"]
  Topology.LoopPrespectrum.Telescope.diagramFunctor

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeDiagram.lean:49-55"
  "adaptation" "The coefficient action preserves each original cylinder coordinate"]
  Topology.LoopPrespectrum.Telescope.diagramFunctor_map_cylinder

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeDiagram.lean:57-62"
  "adaptation" "The actual initial cylinder faces form a natural transformation"]
  Topology.LoopPrespectrum.Telescope.diagramInclusion

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeDiagram.lean:64-74"
  "adaptation" "The consecutive inclusion homotopy is the original quotient cylinder"]
  Topology.LoopPrespectrum.Telescope.diagramInclusionHomotopy
  Topology.LoopPrespectrum.Telescope.diagramInclusionHomotopy_apply

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeDiagram.lean:49-74"
  "adaptation" "Same-time naturality of the literal quotient-cylinder inclusion homotopy"]
  Topology.LoopPrespectrum.Telescope.diagramInclusionHomotopy_naturality_apply
