/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCell
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeRowSeedComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentTransition
public import Colib.KTheory.Bass.ModelRowZigzagBackward

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

/-- The forward map is constructed from the independent cell and original whole source null. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:44"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def forward (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X) ⟶
      ModelDiagramRowStabilizedTarget.target squareFunctor i M X :=
  SchemeRowSeed.seed ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i)
    X (cell M unit hunit i X)

/-- The whole independently constructed cell has the original current-track comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:53"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
theorem cell_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    cell M unit hunit i X =
      ((SchemeNaturalSeed.stageTrack
        (ofModelUnits laurent.op coefficient M unit hunit) i).homotopy X).postcomp
        ((DiagramRowRefinement.comparison
          ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
          (stage squareFunctor M i) (stage_point squareFunctor M i)
          (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i)).app
          (laurent.op.obj X)) := by
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact congrArg (fun f => f.map n x)
    (iteratedCell_at_eq laurent.op coefficient M unit hunit squareFunctor
      (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ))))
      (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ)))) i X t)

/-- The same forward map agrees with the original current seed through the actual row map. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:74"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
theorem forward_eq_seed (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    forward M unit hunit i X =
      (SchemeNaturalSeed.seed
        (SchemeNaturalSeed.stageTrack (ofModelUnits laurent.op coefficient M unit hunit) i)).app X ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison squareFunctor i M X) :=
  SchemeRowSeed.seed_eq _ _ _ _ _ _ _ _ (cell_eq M unit hunit i X)

@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:81"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
private theorem insert_successor_transport {E B B' D : LoopPrespectrum.{w}}
    (h : B' = B) (f : E ⟶ B) (g : B ⟶ D) :
    f ≫ g = (f ≫ eqToHom h.symm) ≫ (eqToHom h ≫ g) := by
  subst B'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The independently formed forward leg has the exact original current-transition factorization. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:88"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
theorem forward_eq_current (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    forward M unit hunit i X =
      (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i := by
  rw [forward_eq_seed, ModelRowZigzagSequentialization.backward_eq]
  simp only [SchemeNaturalSeed.currentTransition, NatTrans.comp_app, eqToHom_app]
  exact insert_successor_transport (ModelDiagramSuspension.successor_obj squareFunctor i M X)
    ((SchemeNaturalSeed.seed
      (SchemeNaturalSeed.stageTrack (ofModelUnits laurent.op coefficient M unit hunit) i)).app X)
    (parameterLoopingMap (ModelDiagramRowRefinement.comparison squareFunctor i M X))

end KTheory.Bass.SchemeModelRowSeed

attribute [colib_tag "COL-0555"]
  KTheory.Bass.SchemeModelRowSeed.forward

attribute [colib_tag "COL-0555"]
  KTheory.Bass.SchemeModelRowSeed.forward_eq_current
