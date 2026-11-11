module
import Colib.KTheory.Bass.StrictDiagramIndexRowTelescopeNaturality
open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.StrictDiagramIndexRow KTheory.Bass.StrictDiagramIndexChange
noncomputable section
universe u₁ v₁ u₂ v₂ w
namespace Test0
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F F' : D ⥤ LoopPrespectrum.{w}} {G G' : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ≅ G) (ρ' : K ⋙ F' ≅ G') (τ : F ⟶ F') (σ : G ⟶ G')
    (h : Functor.whiskerLeft K τ ≫ ρ'.hom = ρ.hom ≫ σ)

example (i : ℕ) :
    Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map τ) ≫
        (finiteIso K Q₁ Q₂ α ρ' i).hom =
      (finiteIso K Q₁ Q₂ α ρ i).hom ≫ (strictDiagramIterate Q₁ i).map σ :=
  finiteIso_naturality K Q₁ Q₂ α ρ ρ' τ σ h i
end Test0
namespace Test1
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

example :
    Functor.whiskerLeft K (seedTelescopeMap Q₂ η₂ η₂' τ h₂) ≫
        telescopeMap K Q₁ Q₂ α ρ' η₂' η₁' hseed' =
      telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed ≫ seedTelescopeMap Q₁ η₁ η₁' σ h₁ :=
  telescopeMap_naturality K Q₁ Q₂ α ρ ρ' τ σ hrow η₂ η₂' η₁ η₁' h₂ h₁ hseed hseed'
end Test1
