/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Bass.StrictDiagramIndexRowMapTelescope
public import Colib.KTheory.Bass.StrictDiagramIndexRowTelescopeNaturality
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# Naturality and stable comparison for forward index and row telescope maps

An arbitrary specified row transformation gives a forward comparison of the original
telescopes. A whole input square commutes literally on every cylinder, by the actual
finite-map naturality square. Pointwise stable finite maps induce a stable comparison
when both original towers have levelwise T1 spaces. No inverse row map is required.
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
    {F F' : D ⥤ LoopPrespectrum.{w}} {G G' : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ⟶ G) (ρ' : K ⋙ F' ⟶ G') (τ : F ⟶ F') (σ : G ⟶ G')
    (hrow : Functor.whiskerLeft K τ ≫ ρ' = ρ ≫ σ)
    (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₂' : F' ⟶ (strictDiagramFunctor Q₂).obj F')
    (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
    (η₁' : G' ⟶ (strictDiagramFunctor Q₁).obj G')
    (h₂ : η₂ ≫ (strictDiagramFunctor Q₂).map τ = τ ≫ η₂')
    (h₁ : η₁ ≫ (strictDiagramFunctor Q₁).map σ = σ ≫ η₁')
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
      (strictDiagramFunctor Q₁).map ρ = ρ ≫ η₁)
    (hseed' : Functor.whiskerLeft K η₂' ≫ (iso K Q₁ Q₂ α F').hom ≫
      (strictDiagramFunctor Q₁).map ρ' = ρ' ≫ η₁')

include hrow in
/-- The complete forward telescope square preserves each original cylinder and its height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMapTelescopeNaturality.lean:46"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
theorem telescopeMap_naturality :
    Functor.whiskerLeft K (StrictDiagramIndexRow.seedTelescopeMap Q₂ η₂ η₂' τ h₂) ≫
        telescopeMap K Q₁ Q₂ α ρ' η₂' η₁' hseed' =
      telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed ≫
        StrictDiagramIndexRow.seedTelescopeMap Q₁ η₁ η₁' σ h₁ := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i s x
  change Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj G').obj X)
      (fun j => (strictDiagramTransition Q₁ η₁' j).app X) n i
      (s, ((finiteMap K Q₁ Q₂ α ρ' i).app X).map n
        ((((strictDiagramIterate Q₂ i).map τ).app (K.obj X)).map n x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj G').obj X)
      (fun j => (strictDiagramTransition Q₁ η₁' j).app X) n i
      (s, (((strictDiagramIterate Q₁ i).map σ).app X).map n
        (((finiteMap K Q₁ Q₂ α ρ i).app X).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => ((strictDiagramIterate Q₁ j).obj G').obj X)
    (fun j => (strictDiagramTransition Q₁ η₁' j).app X) n i (s, y))
    (congrArg (fun k => k.map n x)
      (NatTrans.congr_app (finiteMap_naturality K Q₁ Q₂ α ρ ρ' τ σ hrow i) X))

/-- Actual pointwise stable finite maps induce a stable forward telescope comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexRowMapTelescopeNaturality.lean:70"
  "adaptation" "Original forward row transformation, full telescope square and stable comparison"]
theorem telescopeMap_stable (X : C)
    [∀ i n, T1Space ((((strictDiagramIterate Q₂ i).obj F).obj (K.obj X)).space n)]
    [∀ i n, T1Space ((((strictDiagramIterate Q₁ i).obj G).obj X).space n)]
    (hfinite : ∀ i, IsStableEquivalence ((finiteMap K Q₁ Q₂ α ρ i).app X)) :
    IsStableEquivalence ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X) :=
  Telescope.map_isStableEquivalence
    (fun i => ((strictDiagramIterate Q₂ i).obj F).obj (K.obj X))
    (fun i => (strictDiagramTransition Q₂ η₂ i).app (K.obj X))
    (fun i => ((strictDiagramIterate Q₁ i).obj G).obj X)
    (fun i => (strictDiagramTransition Q₁ η₁ i).app X)
    (fun i => (finiteMap K Q₁ Q₂ α ρ i).app X)
    (fun i => (NatTrans.congr_app (transition_square K Q₁ Q₂ α ρ η₂ η₁ hseed i) X).symm)
    hfinite

end KTheory.Bass.StrictDiagramIndexRowMap

namespace KTheory.Bass.StrictDiagramIndexRowMap

attribute [colib_tag "COL-0586"]
  telescopeMap_naturality

attribute [colib_tag "COL-0586"]
  telescopeMap_stable

end KTheory.Bass.StrictDiagramIndexRowMap
