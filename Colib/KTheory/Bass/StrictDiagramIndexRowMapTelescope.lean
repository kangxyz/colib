/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.StrictDiagramIndexRowMapNaturality

/-! # Actual index change followed by a specified row transformation

The finite maps are the existing index comparison followed by the iterated image of the
specified row transformation. A proved original seed square yields their transition squares.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexRowMap
open StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F : D ⥤ LoopPrespectrum.{w}} {G : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ⟶ G)

variable (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
      (strictDiagramFunctor Q₁).map ρ = ρ ≫ η₁)

/-- The actual finite index maps descend with their unchanged telescope height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMapTelescope.lean:33"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
def telescopeMap : K ⋙ telescope Q₂ η₂ ⟶ telescope Q₁ η₁ :=
  Telescope.diagramMap (fun i => K ⋙ (strictDiagramIterate Q₂ i).obj F)
    (fun i => (strictDiagramIterate Q₁ i).obj G)
    (fun i => Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i))
    (strictDiagramTransition Q₁ η₁) (fun i => finiteMap K Q₁ Q₂ α ρ i)
    (fun i => (transition_square K Q₁ Q₂ α ρ η₂ η₁ hseed i).symm)

/-- The forward map preserves the entire original quotient cylinder. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMapTelescope.lean:41"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
theorem telescopeMap_cylinder (X : C) (n i : ℕ) (s : unitInterval)
    (x : ((strictDiagramIterate Q₂ i).obj F |>.obj (K.obj X)).space n) :
    ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate Q₂ j).obj F).obj (K.obj X))
        (fun j => (strictDiagramTransition Q₂ η₂ j).app (K.obj X)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj G).obj X)
      (fun j => (strictDiagramTransition Q₁ η₁ j).app X) n i
      (s, ((finiteMap K Q₁ Q₂ α ρ i).app X).map n x) := rfl

/-- The original stage inclusion commutes with the same actual index map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMapTelescope.lean:51"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
theorem telescopeMap_inclusion (i : ℕ) :
    Functor.whiskerLeft K (Telescope.diagramInclusion
        (fun j => (strictDiagramIterate Q₂ j).obj F) (strictDiagramTransition Q₂ η₂) i) ≫
        telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed =
      finiteMap K Q₁ Q₂ α ρ i ≫ Telescope.diagramInclusion
        (fun j => (strictDiagramIterate Q₁ j).obj G)
        (strictDiagramTransition Q₁ η₁) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

end KTheory.Bass.StrictDiagramIndexRowMap
