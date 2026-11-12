/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.StrictDiagramIndexTelescope

/-! # Actual index change followed by a specified row map

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

/-- The actual finite index comparison followed by a specified row transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMap.lean:28"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
def finiteMap (i : ℕ) :
    K ⋙ (strictDiagramIterate Q₂ i).obj F ⟶ (strictDiagramIterate Q₁ i).obj G :=
  (iterateIso K Q₁ Q₂ α i F).hom ≫ (strictDiagramIterate Q₁ i).map ρ

variable (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
      (strictDiagramFunctor Q₁).map ρ = ρ ≫ η₁)

include hseed in
/-- The actual seed square preserves all original finite tower transitions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMap.lean:39"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
theorem transition_square (i : ℕ) :
    Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) ≫
        finiteMap K Q₁ Q₂ α ρ (i + 1) =
      finiteMap K Q₁ Q₂ α ρ i ≫ strictDiagramTransition Q₁ η₁ i := by
  change Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map η₂) ≫
      (((iterateIso K Q₁ Q₂ α i ((strictDiagramFunctor Q₂).obj F)).hom ≫
        (strictDiagramIterate Q₁ i).map (iso K Q₁ Q₂ α F).hom) ≫
        (strictDiagramIterate Q₁ i).map ((strictDiagramFunctor Q₁).map ρ)) =
    ((iterateIso K Q₁ Q₂ α i F).hom ≫ (strictDiagramIterate Q₁ i).map ρ) ≫
      (strictDiagramIterate Q₁ i).map η₁
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← Category.assoc,
    iterateIso_naturality, Category.assoc, ← CategoryTheory.Functor.map_comp,
    hseed, CategoryTheory.Functor.map_comp, ← Category.assoc]

end KTheory.Bass.StrictDiagramIndexRowMap
