/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentCoefficient
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquareFactor
public import Colib.KTheory.Bass.ModelUnitRowCellIteration

/-! # Original SchemeModelRowSeed declarations required by returned tensor strictification

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
open ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))

/-- The actual independently iterated cell at the original scheme Bass stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:36"
  "adaptation" "Original actual row data and tensor-started recursion"]
abbrev cell (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  iteratedCell laurent.op coefficient M unit hunit squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i X

end KTheory.Bass.SchemeModelRowSeed
