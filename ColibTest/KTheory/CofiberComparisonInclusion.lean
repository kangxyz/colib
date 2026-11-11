module
import Colib.KTheory.Bass.CofiberComparisonInclusion
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]
  {F₀ F₁ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁)
example (X : C) :
    Homotopy ((f ≫ coneInclusion f).app X)
      ((diagramZeroMap F₀ (mappingConeDiagram f)).app X) :=
  coneNull f X

example {X Y : C} (k : X ⟶ Y) n r x :
    ((mappingConeDiagram f).map k).map n ((coneNull f X).level n (r, x)) =
      (coneNull f Y).level n (r, (F₀.map k).map n x) :=
  coneNull_naturality f k n r x

example :
    mappingConeDescTransformation f (coneInclusion f) (coneNull f)
      (coneNull_naturality f) = 𝟙 (mappingConeDiagram f) :=
  coneDesc_self f

variable (Q : C ⥤ Arrow (Arrow C))
example (X : C) :
    (strictDiagramCofiberComparison Q f).app X =
      mappingConeDesc (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map (coneInclusion f)).app X)
        (strictDiagramNullHomotopy f (coneInclusion f) (coneNull f)
          (coneNull_naturality f) Q X) :=
  cofiberComparison_desc f Q X

example (X : C) :
    mappingConeInclusion (((strictDiagramFunctor Q).map f).app X) ≫
      (strictDiagramCofiberComparison Q f).app X =
        (((strictDiagramFunctor Q).map (coneInclusion f)).app X) :=
  cofiberComparison_inclusion f Q X

example (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F₀).obj X).space n) :
    ((strictDiagramCofiberComparison Q f).app X).map n
      ((mappingConeHomotopy (((strictDiagramFunctor Q).map f).app X)).level n (r, x)) =
        (((strictDiagramFunctor Q).map
          (diagramHomotopyAt (coneNull f) (coneNull_naturality f) r)).app X).map n x :=
  cofiberComparison_cylinder f Q X n r x

end KTheory.Bass.PushoutCofiberSquare
