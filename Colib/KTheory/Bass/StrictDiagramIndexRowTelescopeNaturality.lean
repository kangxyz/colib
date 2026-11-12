/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramIndexRowNaturality
public import Colib.KTheory.Bass.StrictDiagramMap

/-!
# Whole-telescope naturality of actual index and row comparisons

The original seed-preserving diagram maps act through their original finite iterates.
The finite row square descends to the entire quotient telescope, retaining each stage
and cylinder height. No stagewise-isomorphism inference replaces this quotient proof.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexRow
open StrictDiagramIndexChange

/-- The original finite images of a seed-preserving map descend through the telescope. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramIndexRowTelescopeNaturality.lean:26"
  "adaptation" "Original complete finite and quotient-telescope row naturality."]
def seedTelescopeMap {C : Type u₁} [Category.{v₁} C]
    (Q : C ⥤ Arrow (Arrow C)) {F G : C ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ (strictDiagramFunctor Q).obj F)
    (θ : G ⟶ (strictDiagramFunctor Q).obj G) (τ : F ⟶ G)
    (h : η ≫ (strictDiagramFunctor Q).map τ = τ ≫ θ) :
    telescope Q η ⟶ telescope Q θ :=
  Telescope.diagramMap (fun i => (strictDiagramIterate Q i).obj F)
    (fun i => (strictDiagramIterate Q i).obj G)
    (strictDiagramTransition Q η) (strictDiagramTransition Q θ)
    (fun i => (strictDiagramIterate Q i).map τ)
    (fun i => (strictDiagramTransition_map Q η θ τ h i).symm)

/-- The same finite map acts at each original stage and full telescope height. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramIndexRowTelescopeNaturality.lean:39"
  "adaptation" "Original complete finite and quotient-telescope row naturality."]
theorem seedTelescopeMap_cylinder {C : Type u₁} [Category.{v₁} C]
    (Q : C ⥤ Arrow (Arrow C)) {F G : C ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ (strictDiagramFunctor Q).obj F)
    (θ : G ⟶ (strictDiagramFunctor Q).obj G) (τ : F ⟶ G)
    (h : η ≫ (strictDiagramFunctor Q).map τ = τ ≫ θ)
    (X : C) (n i : ℕ) (s : unitInterval)
    (x : ((strictDiagramIterate Q i).obj F |>.obj X).space n) :
    ((seedTelescopeMap Q η θ τ h).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate Q j).obj F).obj X)
        (fun j => (strictDiagramTransition Q η j).app X) n i (s,x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q j).obj G).obj X)
      (fun j => (strictDiagramTransition Q θ j).app X) n i
      (s, (((strictDiagramIterate Q i).map τ).app X).map n x) := rfl

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F F' : D ⥤ LoopPrespectrum.{w}} {G G' : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ≅ G) (ρ' : K ⋙ F' ≅ G') (τ : F ⟶ F') (σ : G ⟶ G')
    (hrow : Functor.whiskerLeft K τ ≫ ρ'.hom = ρ.hom ≫ σ)
    (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₂' : F' ⟶ (strictDiagramFunctor Q₂).obj F')
    (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
    (η₁' : G' ⟶ (strictDiagramFunctor Q₁).obj G')
    (h₂ : η₂ ≫ (strictDiagramFunctor Q₂).map τ = τ ≫ η₂')
    (h₁ : η₁ ≫ (strictDiagramFunctor Q₁).map σ = σ ≫ η₁')
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
      (strictDiagramFunctor Q₁).map ρ.hom = ρ.hom ≫ η₁)
    (hseed' : Functor.whiskerLeft K η₂' ≫ (iso K Q₁ Q₂ α F').hom ≫
      (strictDiagramFunctor Q₁).map ρ'.hom = ρ'.hom ≫ η₁')

include hrow in
/-- The complete original telescope square follows from the actual finite row squares. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramIndexRowTelescopeNaturality.lean:72"
  "adaptation" "Original complete finite and quotient-telescope row naturality."]
theorem telescopeMap_naturality :
    Functor.whiskerLeft K (seedTelescopeMap Q₂ η₂ η₂' τ h₂) ≫
        telescopeMap K Q₁ Q₂ α ρ' η₂' η₁' hseed' =
      telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed ≫ seedTelescopeMap Q₁ η₁ η₁' σ h₁ := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i s x
  change Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj G').obj X)
      (fun j => (strictDiagramTransition Q₁ η₁' j).app X) n i
      (s, ((finiteIso K Q₁ Q₂ α ρ' i).hom.app X).map n
        ((((strictDiagramIterate Q₂ i).map τ).app (K.obj X)).map n x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj G').obj X)
      (fun j => (strictDiagramTransition Q₁ η₁' j).app X) n i
      (s, (((strictDiagramIterate Q₁ i).map σ).app X).map n
        (((finiteIso K Q₁ Q₂ α ρ i).hom.app X).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => ((strictDiagramIterate Q₁ j).obj G').obj X)
    (fun j => (strictDiagramTransition Q₁ η₁' j).app X) n i (s,y))
    (congrArg (fun k => k.map n x)
      (NatTrans.congr_app (finiteIso_naturality K Q₁ Q₂ α ρ ρ' τ σ hrow i) X))

end KTheory.Bass.StrictDiagramIndexRow
