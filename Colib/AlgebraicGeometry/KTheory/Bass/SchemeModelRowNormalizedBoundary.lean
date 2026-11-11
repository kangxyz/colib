/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCell
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeRowDiagonal
public import Colib.KTheory.Bass.DiagramRowNormalizedBoundary

/-! # Original SchemeModelRowNormalizedBoundary declarations required by returned tensor
      strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeModelRowSeed
open NaturalTrack ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))


/-- Normalize the genuine independently iterated cell before the actual boundary inclusion. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowNormalizedBoundary.lean:36"
  "adaptation" "Original actual row data and tensor-started recursion"]
def normalizedBoundary (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X) ⟶
      parameterLooping (DiagramRowSeed.carrier squareFunctor
        ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
        (stage squareFunctor M i) (stage_point squareFunctor M i)
        (stage_naturality squareFunctor M i) X) :=
  DiagramRowSeed.normalizedBoundary squareFunctor
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X (cell M unit hunit i X))

end KTheory.Bass.SchemeModelRowSeed
