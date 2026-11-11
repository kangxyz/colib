module
import Colib.KTheory.Bass.StrictDiagramIndexRowMapTelescopeNaturality

open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open StrictDiagramIndexChange StrictDiagramIndexRowMap
noncomputable section
universe u₁ v₁ u₂ v₂ w
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

example (i : ℕ) :
    finiteMap K Q₁ Q₂ α ρ i =
      (iterateIso K Q₁ Q₂ α i F).hom ≫ (strictDiagramIterate Q₁ i).map ρ := rfl

example (i : ℕ) :
    Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) ≫
        finiteMap K Q₁ Q₂ α ρ (i + 1) =
      finiteMap K Q₁ Q₂ α ρ i ≫ strictDiagramTransition Q₁ η₁ i :=
  transition_square K Q₁ Q₂ α ρ η₂ η₁ hseed i

example (i : ℕ) :
    Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map τ) ≫
        finiteMap K Q₁ Q₂ α ρ' i =
      finiteMap K Q₁ Q₂ α ρ i ≫ (strictDiagramIterate Q₁ i).map σ :=
  finiteMap_naturality K Q₁ Q₂ α ρ ρ' τ σ hrow i

example : K ⋙ telescope Q₂ η₂ ⟶ telescope Q₁ η₁ :=
  telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed

example (X : C) (n i : ℕ) (s : unitInterval)
    (x : ((strictDiagramIterate Q₂ i).obj F |>.obj (K.obj X)).space n) :
    ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X).map n
      (Telescope.cylinder (fun j ↦ ((strictDiagramIterate Q₂ j).obj F).obj (K.obj X))
        (fun j ↦ (strictDiagramTransition Q₂ η₂ j).app (K.obj X)) n i (s, x)) =
    Telescope.cylinder (fun j ↦ ((strictDiagramIterate Q₁ j).obj G).obj X)
      (fun j ↦ (strictDiagramTransition Q₁ η₁ j).app X) n i
      (s, ((finiteMap K Q₁ Q₂ α ρ i).app X).map n x) :=
  telescopeMap_cylinder K Q₁ Q₂ α ρ η₂ η₁ hseed X n i s x

example (i : ℕ) :
    Functor.whiskerLeft K (Telescope.diagramInclusion
        (fun j ↦ (strictDiagramIterate Q₂ j).obj F) (strictDiagramTransition Q₂ η₂) i) ≫
        telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed =
      finiteMap K Q₁ Q₂ α ρ i ≫ Telescope.diagramInclusion
        (fun j ↦ (strictDiagramIterate Q₁ j).obj G)
        (strictDiagramTransition Q₁ η₁) i :=
  telescopeMap_inclusion K Q₁ Q₂ α ρ η₂ η₁ hseed i

example :
    Functor.whiskerLeft K (StrictDiagramIndexRow.seedTelescopeMap Q₂ η₂ η₂' τ h₂) ≫
        telescopeMap K Q₁ Q₂ α ρ' η₂' η₁' hseed' =
      telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed ≫
        StrictDiagramIndexRow.seedTelescopeMap Q₁ η₁ η₁' σ h₁ :=
  telescopeMap_naturality K Q₁ Q₂ α ρ ρ' τ σ hrow η₂ η₂' η₁ η₁' h₂ h₁ hseed hseed'

example (X : C)
    [∀ i n, T1Space ((((strictDiagramIterate Q₂ i).obj F).obj (K.obj X)).space n)]
    [∀ i n, T1Space ((((strictDiagramIterate Q₁ i).obj G).obj X).space n)]
    (hfinite : ∀ i, IsStableEquivalence ((finiteMap K Q₁ Q₂ α ρ i).app X)) :
    IsStableEquivalence ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X) :=
  telescopeMap_stable K Q₁ Q₂ α ρ η₂ η₁ hseed X hfinite

example (X : C) (k : ℕ)
    [∀ i n, T1Space ((((strictDiagramIterate Q₂ i).obj F).obj (K.obj X)).space n)]
    [∀ i n, T1Space ((((strictDiagramIterate Q₁ i).obj G).obj X).space n)]
    (hfinite : ∀ i, IsStableEquivalence ((finiteMap K Q₁ Q₂ α ρ i).app X)) :
    IsIso ((stableHomotopyFunctor (-(k : ℤ) - 1)).map
      ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X)) :=
  telescopeMap_stable K Q₁ Q₂ α ρ η₂ η₁ hseed X hfinite (-(k : ℤ) - 1)
