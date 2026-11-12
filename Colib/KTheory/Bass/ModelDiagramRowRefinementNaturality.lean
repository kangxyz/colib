/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowComparison
public import Colib.KTheory.Bass.ModelDiagramRowStability
public import Colib.Topology.Prespectrum.RowRefinementFunctoriality

/-!
# Natural stable row comparisons of actual finite Bass diagrams

The computed row action is natural under the original index arrows. It therefore supplies
an actual diagram of row targets and a natural comparison from the original cone diagram.
Both functor laws and the comparison square retain the explicit zero-level loop extension.
Every component, and its parameter-looped component, is the previously proved stable map.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The original unlooped cone diagram at this actual finite Bass stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:29"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
abbrev sourceDiagram : C ⥤ LoopPrespectrum.{w} :=
  ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))

/-- Each original index arrow acts on the complete row-compatible target. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:33"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def map {X Y : C} (f : X ⟶ Y) : carrier Q i F X ⟶ carrier Q i F Y :=
  RowRefinement.map (ModelDiagramRowInterchange.cone Q i F X)
    (ModelDiagramRowInterchange.cone Q i F Y)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F Y)
    ((sourceDiagram Q i F).map f) (ModelDiagramRowInterchange.cone_naturality Q i F f)

/-- The actual identity arrow acts identically, including both degree-zero loop parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:41"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem map_id (X : C) : map Q i F (𝟙 X) = 𝟙 (carrier Q i F X) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  cases n with
  | zero =>
    change Path (Path.refl ((source Q i F X).point 2))
      (Path.refl ((source Q i F X).point 2)) at γ
    apply Path.ext; funext r; apply Path.ext; funext s
    exact congrArg (fun a => a.map 2 (γ r s)) ((sourceDiagram Q i F).map_id X)
  | succ k =>
    change Path ((source Q i F X).point (k + 2)) ((source Q i F X).point (k + 2)) at γ
    apply Path.ext; funext s
    exact congrArg (fun a => a.map (k + 2) (γ s)) ((sourceDiagram Q i F).map_id X)

/-- Composition follows the original index composition without changing the row clock. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:58"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map Q i F (f ≫ g) = map Q i F f ≫ map Q i F g := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  cases n with
  | zero =>
    change Path (Path.refl ((source Q i F X).point 2))
      (Path.refl ((source Q i F X).point 2)) at γ
    apply Path.ext; funext r; apply Path.ext; funext s
    exact congrArg (fun a => a.map 2 (γ r s)) ((sourceDiagram Q i F).map_comp f g)
  | succ k =>
    change Path ((source Q i F X).point (k + 2)) ((source Q i F X).point (k + 2)) at γ
    apply Path.ext; funext s
    exact congrArg (fun a => a.map (k + 2) (γ s)) ((sourceDiagram Q i F).map_comp f g)

/-- The actual cone refinement is a functor on the unchanged indexing category. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:76"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def diagram : C ⥤ LoopPrespectrum.{w} where
  obj := carrier Q i F
  map := map Q i F
  map_id := map_id Q i F
  map_comp := map_comp Q i F

/-- The original cone map and the actual whole row comparison form a strict square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:83"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem comparison_naturality {X Y : C} (f : X ⟶ Y) :
    (sourceDiagram Q i F).map f ≫ comparison Q i F Y =
      comparison Q i F X ≫ map Q i F f :=
  RowRefinement.comparison_naturality
    (ModelDiagramRowInterchange.cone Q i F X) (ModelDiagramRowInterchange.cone Q i F Y)
    (ModelDiagramRowInterchange.cone_point Q i F X)
    (ModelDiagramRowInterchange.cone_point Q i F Y)
    ((sourceDiagram Q i F).map f) (ModelDiagramRowInterchange.cone_naturality Q i F f)
    (ModelDiagramRowInterchange.cone_structure Q i F X)
    (ModelDiagramRowInterchange.cone_structure Q i F Y)

/-- The actual stable comparisons constitute a natural transformation of whole diagrams. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:95"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def comparisonNatTrans : sourceDiagram Q i F ⟶ diagram Q i F where
  app := comparison Q i F
  naturality _ _ := comparison_naturality Q i F

/-- Every component is stable by the proved actual finite-stage range. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:100"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem comparisonNatTrans_isStableEquivalence (X : C) :
    IsStableEquivalence ((comparisonNatTrans Q i F).app X) :=
  comparison_isStableEquivalence Q i F X

/-- Parameter looping retains the complete natural comparison, not just its stable classes. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:105"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def parameterComparisonNatTrans :
    sourceDiagram Q i F ⋙ parameterLoopingFunctor ⟶ diagram Q i F ⋙ parameterLoopingFunctor :=
  Functor.whiskerRight (comparisonNatTrans Q i F) parameterLoopingFunctor

/-- All parameter-looped components are the original actual stable roof arrows. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowRefinementNaturality.lean:110"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem parameterComparisonNatTrans_isStableEquivalence (X : C) :
    IsStableEquivalence ((parameterComparisonNatTrans Q i F).app X) :=
  parameterComparison_isStableEquivalence Q i F X

end KTheory.Bass.ModelDiagramRowRefinement
