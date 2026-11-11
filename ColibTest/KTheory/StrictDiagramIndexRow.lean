module
import Colib.KTheory.Bass.StrictDiagramIndexRowTelescope

open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.StrictDiagramIndexChange
universe u₁ v₁ u₂ v₂ w
noncomputable section
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
  (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
  {F : D ⥤ LoopPrespectrum.{w}} {G : C ⥤ LoopPrespectrum.{w}} (ρ : K ⋙ F ≅ G)
  (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
  (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
  (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
    (strictDiagramFunctor Q₁).map ρ.hom = ρ.hom ≫ η₁)

example (i : ℕ) :
    K ⋙ (strictDiagramIterate Q₂ i).obj F ≅ (strictDiagramIterate Q₁ i).obj G :=
  StrictDiagramIndexRow.finiteIso K Q₁ Q₂ α ρ i

example (i : ℕ) :
    Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) ≫
        (StrictDiagramIndexRow.finiteIso K Q₁ Q₂ α ρ (i + 1)).hom =
      (StrictDiagramIndexRow.finiteIso K Q₁ Q₂ α ρ i).hom ≫
        strictDiagramTransition Q₁ η₁ i :=
  StrictDiagramIndexRow.transition_square K Q₁ Q₂ α ρ η₂ η₁ hseed i

example (X : C) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate Q₂ i).obj F).obj (K.obj X)).space n) :
    ((StrictDiagramIndexRow.telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X).map n
        (Telescope.cylinder (fun j => ((strictDiagramIterate Q₂ j).obj F).obj (K.obj X))
          (fun j => (strictDiagramTransition Q₂ η₂ j).app (K.obj X)) n i (s, x)) =
      Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj G).obj X)
        (fun j => (strictDiagramTransition Q₁ η₁ j).app X) n i
        (s, ((StrictDiagramIndexRow.finiteIso K Q₁ Q₂ α ρ i).hom.app X).map n x) :=
  StrictDiagramIndexRow.telescopeMap_cylinder K Q₁ Q₂ α ρ η₂ η₁ hseed X n i s x

example :
    StrictDiagramIndexRow.telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed ≫
      StrictDiagramIndexRow.telescopeInv K Q₁ Q₂ α ρ η₂ η₁ hseed = 𝟙 _ :=
  StrictDiagramIndexRow.telescopeMap_inv K Q₁ Q₂ α ρ η₂ η₁ hseed

example (i : ℕ) :
    Functor.whiskerLeft K (Telescope.diagramInclusion
        (fun j => (strictDiagramIterate Q₂ j).obj F) (strictDiagramTransition Q₂ η₂) i) ≫
        StrictDiagramIndexRow.telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed =
      (StrictDiagramIndexRow.finiteIso K Q₁ Q₂ α ρ i).hom ≫ Telescope.diagramInclusion
        (fun j => (strictDiagramIterate Q₁ j).obj G) (strictDiagramTransition Q₁ η₁) i :=
  StrictDiagramIndexRow.telescopeMap_inclusion K Q₁ Q₂ α ρ η₂ η₁ hseed i

example (X : C) :
    IsStableEquivalence
      ((StrictDiagramIndexRow.telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X) :=
  StrictDiagramIndexRow.telescopeMap_stable K Q₁ Q₂ α ρ η₂ η₁ hseed X
