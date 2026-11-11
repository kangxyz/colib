/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelUnitRowCellStrictification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedBoundary

/-! # Original SchemeModelRowCellStrictification declarations required by returned tensor
      strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeModelRowStrictification
open ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))
  (R : ∀ X, M.obj X ⟶ M.obj (laurent.op.obj X))
  (e : ∀ X, (M.map (coefficient.app X)).hom.toFunctor ≅ (R X).hom.toFunctor)
  (μ : ∀ X, (R X).hom.toFunctor ⟶ (R X).hom.toFunctor)
  (he : ∀ X, (onFunctor (M.map (coefficient.app X)).hom.toFunctor (unit X)).hom ≫ (e X).hom =
    (e X).hom ≫ μ X)

/-- Iterate the actual returned-action cell on the original scheme squares. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowCellStrictification.lean:38"
  "adaptation" "Original actual row data and tensor-started recursion"]
def iteratedCell (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (ModelUnitRowStrictification.iteratedFamily laurent.op coefficient M unit hunit R e μ he
    squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i).val X

/-- The complete independently iterated cell agrees with the original cell at every stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowCellStrictification.lean:47"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem iteratedCell_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    iteratedCell M unit hunit R e μ he i X = SchemeModelRowSeed.cell M unit hunit i X :=
  ModelUnitRowStrictification.iteratedCell_eq laurent.op coefficient M unit hunit R e μ he
    squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i X

/-- Normalize each independently constructed returned-action cell before its original boundary. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowCellStrictification.lean:57"
  "adaptation" "Original actual row data and tensor-started recursion"]
def normalizedForward (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  DiagramRowSeed.normalizedBoundary squareFunctor
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X (iteratedCell M unit hunit R e μ he i X))

/-- Original normalized forward maps are identified after the actual returned-action recursion. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowCellStrictification.lean:65"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem normalizedForward_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    normalizedForward M unit hunit R e μ he i X =
      SchemeModelRowSeed.normalizedBoundary M unit hunit i X := by
  unfold normalizedForward
  rw [iteratedCell_eq]
  rfl

end KTheory.Bass.SchemeModelRowStrictification
