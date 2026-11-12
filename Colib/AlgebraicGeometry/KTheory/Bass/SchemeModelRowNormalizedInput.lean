/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowPresentationInput
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedPresentation
public import Colib.KTheory.Bass.DiagramRowNormalizedBoundaryNaturality

/-!
# Actual Model inputs preserve the whole normalized-boundary presentation

The original unit-preserving transformation determines the cell square through
its proved independent-cell comparison. Whole normalization naturality then
retains every normalization time, before descending to the canonical telescope.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeModelRowSeed
open NaturalTrack GeometricSeedCospan ModelRowZigzagSequentialization
open GeometricSquareInterchange ModelDiagramRowInterchange
open scoped _root_.Topology unitInterval
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))
  (M' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit' : ∀ X, 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj)
  (hunit' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M'.map (laurent.op.map g)).hom.toFunctor (unit' X) (unit' Y))
  (η : M ⟶ M')
  (hη : ∀ X, Preserves (η.app (laurent.op.obj X)).hom.toFunctor (unit X) (unit' X))

/-- The actual input map on each refined original finite object. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:43"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def stageRowInput (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.map (stage squareFunctor M i X) (stage squareFunctor M' i X)
    (stage_point squareFunctor M i X) (stage_point squareFunctor M' i X)
    (stageInput M M' η i X) (stage_input_naturality squareFunctor η i X)

/-- Original comparison maps commute with the genuine stage input. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:49"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem stageRowInput_comparison (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    stageInput M M' η i X ≫
        (DiagramRowRefinement.comparison _ (stage squareFunctor M' i)
          (stage_point squareFunctor M' i) (stage_naturality squareFunctor M' i)
          (stage_structure squareFunctor M' i)).app X =
      (DiagramRowRefinement.comparison _ (stage squareFunctor M i)
          (stage_point squareFunctor M i) (stage_naturality squareFunctor M i)
          (stage_structure squareFunctor M i)).app X ≫ stageRowInput M M' η i X :=
  RowRefinement.comparison_naturality _ _ _ _ _ (stage_input_naturality squareFunctor η i X)
    (stage_structure squareFunctor M i X) (stage_structure squareFunctor M' i X)

include hη in
/-- Actual unit preservation propagates to the complete original stage track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:62"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem stageInput_equivariant (i : ℕ) :
    Equivariant
      (SchemeNaturalSeed.stageTrack (ofModelUnits laurent.op coefficient M unit hunit) i)
      (SchemeNaturalSeed.stageTrack (ofModelUnits laurent.op coefficient M' unit' hunit') i)
      ((strictDiagramIterate squareFunctor i).map
        (Functor.whiskerRight η prespectrumFunctor)) :=
  (inputEquivariance M unit hunit M' unit' hunit' η hη).stages
    (L := laurent.op) (c := coefficient) squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i

include hη in
/-- The actual independent cell square retains its original time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:77"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem input_cell_at (i : ℕ) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (cell M unit hunit i X).at t ≫ stageRowInput M M' η i (laurent.op.obj X) =
      stageInput M M' η i X ≫ (cell M' unit' hunit' i X).at t := by
  rw [cell_eq, cell_eq]
  change (((SchemeNaturalSeed.stageTrack
    (ofModelUnits laurent.op coefficient M unit hunit) i).homotopy X).at t ≫ _) ≫ _ =
      _ ≫ (((SchemeNaturalSeed.stageTrack
        (ofModelUnits laurent.op coefficient M' unit' hunit') i).homotopy X).at t ≫ _)
  rw [Category.assoc, ← stageRowInput_comparison, ← Category.assoc]
  simp only [stageInput]
  rw [← stageInput_equivariant M unit hunit M' unit' hunit' η hη i X t, Category.assoc]

include hη in
/-- The normalized independent forward map is natural in the original Model input. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:91"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedInput_forward (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    normalizedBoundary M unit hunit i X ≫ targetInput M M' η i X =
      stageInput M M' η i X ≫ normalizedBoundary M' unit' hunit' i X := by
  apply DiagramRowSeed.normalizedBoundary_naturality squareFunctor
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i)
    (stage squareFunctor M' i) (stage_point squareFunctor M' i)
    (stage_naturality squareFunctor M' i)
    (stage_structure squareFunctor M i) (stage_structure squareFunctor M' i)
    ((strictDiagramIterate squareFunctor i).map (Functor.whiskerRight η prespectrumFunctor))
    (stage_input_naturality squareFunctor η i) X
  intro n t x
  exact congrArg (fun a => a.map n x)
    (input_cell_at M unit hunit M' unit' hunit' η hη i X t)

include hη in
/-- The entire normalization homotopy keeps its time under each actual input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:108"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedInput_homotopy (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s : unitInterval)
    (x : (vertex squareFunctor M X i).space n) :
    (targetInput M M' η i X).map n
        ((normalizedBoundaryCurrentHomotopy M unit hunit i X).level n (s, x)) =
      (normalizedBoundaryCurrentHomotopy M' unit' hunit' i X).level n
        (s, (stageInput M M' η i X).map n x) := by
  apply DiagramRowSeed.normalizedBoundaryHomotopy_naturality_apply squareFunctor
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i)
    (stage squareFunctor M' i) (stage_point squareFunctor M' i)
    (stage_naturality squareFunctor M' i)
    (stage_structure squareFunctor M i) (stage_structure squareFunctor M' i)
    ((strictDiagramIterate squareFunctor i).map (Functor.whiskerRight η prespectrumFunctor))
    (stage_input_naturality squareFunctor η i) X
  intro k t y
  exact congrArg (fun a => a.map k y)
    (input_cell_at M unit hunit M' unit' hunit' η hη i X t)

/-- Actual unit-preserving inputs induce the canonical normalized presentation map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:127"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedInputMap (X : Scheme.{u}ᵒᵖ) :
    normalizedPresentation M unit hunit X ⟶ normalizedPresentation M' unit' hunit' X :=
  ZigzagSequentialization.inducedTelescopeMap
    (vertex squareFunctor M X) (target squareFunctor M X)
    (fun i => normalizedBoundary M unit hunit i X) (backward squareFunctor M X)
    (vertex squareFunctor M' X) (target squareFunctor M' X)
    (fun i => normalizedBoundary M' unit' hunit' i X) (backward squareFunctor M' X)
    (fun i => stageInput M M' η i X) (fun i => targetInput M M' η i X)
    (fun i => normalizedInput_forward M unit hunit M' unit' hunit' η hη i X)
    (fun i => input_backward_square M M' η i X)

/-- The original current input square retains every normalization-cylinder time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInput.lean:139"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedComparison_inputMap (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentInputMap
      (ofModelUnits laurent.op coefficient M unit hunit)
      (ofModelUnits laurent.op coefficient M' unit' hunit')
      (Functor.whiskerRight η prespectrumFunctor)
      (inputEquivariance M unit hunit M' unit' hunit' η hη)).app X ≫
        normalizedComparison M' unit' hunit' X =
      normalizedComparison M unit hunit X ≫
        normalizedInputMap M unit hunit M' unit' hunit' η hη X := by
  exact ZigzagSequentialization.telescopeMap_naturality
    (vertex squareFunctor M X) (target squareFunctor M X)
    (fun i => normalizedBoundary M unit hunit i X) (backward squareFunctor M X)
    (vertex squareFunctor M' X) (target squareFunctor M' X)
    (fun i => normalizedBoundary M' unit' hunit' i X) (backward squareFunctor M' X)
    (fun i => stageInput M M' η i X) (fun i => targetInput M M' η i X)
    (fun i => normalizedInput_forward M unit hunit M' unit' hunit' η hη i X)
    (fun i => input_backward_square M M' η i X)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M' unit' hunit') i).app X)
    (fun i => normalizedBoundaryCurrentHomotopy M unit hunit i X)
    (fun i => normalizedBoundaryCurrentHomotopy M' unit' hunit' i X)
    (fun i n t x => normalizedInput_homotopy M unit hunit M' unit' hunit' η hη i X n t x)
    (fun i => input_current_square M unit hunit M' unit' hunit' η hη i X)

end KTheory.Bass.SchemeModelRowSeed
