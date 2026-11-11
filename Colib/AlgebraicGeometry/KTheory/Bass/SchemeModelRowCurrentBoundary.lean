/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedBoundary
public import Colib.KTheory.Bass.DiagramRowNormalizedBoundaryHomotopy

/-! # The original whole scheme current-transition comparison

The actual original coefficient track, finite-stage seed and literal row target are retained.
No stable class substitutes for the whole map or normalized boundary homotopy.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan NaturalTrack GeometricSquareInterchange ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))

/-- The original normalization prism identifies the entire forward leg in the common row target.
-/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowNormalizedBoundary.lean:47"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def normalizedBoundaryHomotopy (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (normalizedBoundary M unit hunit i X) (forward M unit hunit i X) :=
  DiagramRowSeed.normalizedBoundaryHomotopy squareFunctor
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X (cell M unit hunit i X))

/-- The independently normalized boundary leg has the actual current-transition factorization.
-/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowNormalizedBoundary.lean:57"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def normalizedBoundaryCurrentHomotopy (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (normalizedBoundary M unit hunit i X)
      ((SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i) :=
  (normalizedBoundaryHomotopy M unit hunit i X).cast rfl
    (forward_eq_current M unit hunit i X)

end KTheory.Bass.SchemeModelRowSeed

attribute [colib_tag "COL-0555"]
  KTheory.Bass.SchemeModelRowSeed.normalizedBoundaryHomotopy

attribute [colib_tag "COL-0555"]
  KTheory.Bass.SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy
