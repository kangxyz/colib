/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.StrictDiagramIndexTelescope

/-! # Actual index change followed by a specified row isomorphism

The finite maps are the existing index comparison followed by the iterated image of the
specified row isomorphism. A proved original seed square yields their transition squares.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramIndexRow.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexRow
open StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F : D ⥤ LoopPrespectrum.{w}} {G : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ≅ G)

/-- The prescribed index comparison followed by the original row isomorphism at each stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRow.lean:28"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def finiteIso (i : ℕ) :
    K ⋙ (strictDiagramIterate Q₂ i).obj F ≅ (strictDiagramIterate Q₁ i).obj G :=
  iterateIso K Q₁ Q₂ α i F ≪≫ (strictDiagramIterate Q₁ i).mapIso ρ

variable (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
      (strictDiagramFunctor Q₁).map ρ.hom = ρ.hom ≫ η₁)

include hseed in
/-- The actual seed square preserves all original finite tower transitions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRow.lean:39"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem transition_square (i : ℕ) :
    Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) ≫
        (finiteIso K Q₁ Q₂ α ρ (i + 1)).hom =
      (finiteIso K Q₁ Q₂ α ρ i).hom ≫ strictDiagramTransition Q₁ η₁ i := by
  change Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map η₂) ≫
      (((iterateIso K Q₁ Q₂ α i ((strictDiagramFunctor Q₂).obj F)).hom ≫
        (strictDiagramIterate Q₁ i).map (iso K Q₁ Q₂ α F).hom) ≫
        (strictDiagramIterate Q₁ i).map ((strictDiagramFunctor Q₁).map ρ.hom)) =
    ((iterateIso K Q₁ Q₂ α i F).hom ≫ (strictDiagramIterate Q₁ i).map ρ.hom) ≫
      (strictDiagramIterate Q₁ i).map η₁
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← Category.assoc,
    iterateIso_naturality, Category.assoc, ← CategoryTheory.Functor.map_comp,
    hseed, CategoryTheory.Functor.map_comp, ← Category.assoc]

include hseed in
/-- The specified inverse maps preserve the unchanged tower transitions as well. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRow.lean:55"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem inverse_transition_square (i : ℕ) :
    (finiteIso K Q₁ Q₂ α ρ i).inv ≫
        Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) =
      strictDiagramTransition Q₁ η₁ i ≫ (finiteIso K Q₁ Q₂ α ρ (i + 1)).inv := by
  apply (cancel_mono (finiteIso K Q₁ Q₂ α ρ (i + 1)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [transition_square K Q₁ Q₂ α ρ η₂ η₁ hseed i, Iso.inv_hom_id_assoc]

end KTheory.Bass.StrictDiagramIndexRow

