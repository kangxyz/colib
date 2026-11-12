/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.StrictDiagramIndexRowTelescope

/-! # Whole-row naturality of the original finite index comparisons -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexRow
open StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F F' : D ⥤ LoopPrespectrum.{w}} {G G' : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ≅ G) (ρ' : K ⋙ F' ≅ G') (τ : F ⟶ F') (σ : G ⟶ G')
    (h : Functor.whiskerLeft K τ ≫ ρ'.hom = ρ.hom ≫ σ)

include h in
/-- Every specified whole row square remains exact after all finite original iterations. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramIndexRowNaturality.lean:26"
  "adaptation" "Original complete finite and quotient-telescope row naturality."]
theorem finiteIso_naturality (i : ℕ) :
    Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map τ) ≫
        (finiteIso K Q₁ Q₂ α ρ' i).hom =
      (finiteIso K Q₁ Q₂ α ρ i).hom ≫ (strictDiagramIterate Q₁ i).map σ := by
  change Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map τ) ≫
      ((iterateIso K Q₁ Q₂ α i F').hom ≫ (strictDiagramIterate Q₁ i).map ρ'.hom) =
    ((iterateIso K Q₁ Q₂ α i F).hom ≫ (strictDiagramIterate Q₁ i).map ρ.hom) ≫
      (strictDiagramIterate Q₁ i).map σ
  rw [← Category.assoc, iterateIso_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp, ← Category.assoc]

end KTheory.Bass.StrictDiagramIndexRow
