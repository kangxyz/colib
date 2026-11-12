/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowPresentationMap
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputTelescope

/-!
# Actual Model inputs of the independent proper-row presentation

A unit-preserving exact Model transformation supplies both original finite
squares, hence the actual presentation map and current comparison square.
No finite-stage or telescope compatibility is assumed separately.
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

include hη in
/-- The original Model transformation preserves the entire initial unit track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:41"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inputEquivariance :
    Equivariant (ofModelUnits laurent.op coefficient M unit hunit)
      (ofModelUnits laurent.op coefficient M' unit' hunit')
      (Functor.whiskerRight η prespectrumFunctor) :=
  ofModelUnits_equivariant laurent.op coefficient M unit hunit M' unit' hunit' η hη

/-- The actual Model input at every original finite Bass vertex. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:48"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def stageInput (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    vertex squareFunctor M X i ⟶ vertex squareFunctor M' X i :=
  ((strictDiagramIterate squareFunctor i).map (Functor.whiskerRight η prespectrumFunctor)).app X

/-- The exact input map on each actual computed proper-row target. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:53"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def targetInput (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    target squareFunctor M X i ⟶ target squareFunctor M' X i :=
  (ModelDiagramRowStabilizedTarget.inputNatTrans squareFunctor i η).app X

include hη in
/-- Actual initial unit preservation proves every original current-transition square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:59"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem input_current_square (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    stageInput M M' η i X ≫
      (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M' unit' hunit') i).app X =
    (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
      stageInput M M' η (i + 1) X :=
  congrArg (fun a => a.app X) (SchemeNaturalSeed.currentInput_transition
    (ofModelUnits laurent.op coefficient M unit hunit)
    (ofModelUnits laurent.op coefficient M' unit' hunit')
    (Functor.whiskerRight η prespectrumFunctor)
    (inputEquivariance M unit hunit M' unit' hunit' η hη) i)

/-- The original backward legs preserve the exact input transformation with its genuine casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:73"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem input_backward_square (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    backward squareFunctor M X i ≫ targetInput M M' η i X =
      stageInput M M' η (i + 1) X ≫ backward squareFunctor M' X i :=
  (backward_input_naturality squareFunctor M i η X).symm

/-- The actual input Model map acts on the independently formed proper-row presentation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:79"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def inputMap (X : Scheme.{u}ᵒᵖ) :
    presentation M unit hunit X ⟶ presentation M' unit' hunit' X :=
  finiteMap M unit hunit X M' unit' hunit' X
    (fun i => stageInput M M' η i X) (fun i => targetInput M M' η i X)
    (fun i => input_current_square M unit hunit M' unit' hunit' η hη i X)
    (fun i => input_backward_square M M' η i X)

/-- The comparison square uses the original current input map and the genuine presentation map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationInput.lean:87"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem comparison_inputMap (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentInputMap
      (ofModelUnits laurent.op coefficient M unit hunit)
      (ofModelUnits laurent.op coefficient M' unit' hunit')
      (Functor.whiskerRight η prespectrumFunctor)
      (inputEquivariance M unit hunit M' unit' hunit' η hη)).app X ≫
        comparison M' unit' hunit' X =
      comparison M unit hunit X ≫ inputMap M unit hunit M' unit' hunit' η hη X :=
  comparison_finiteMap M unit hunit X M' unit' hunit' X
    (fun i => stageInput M M' η i X) (fun i => targetInput M M' η i X)
    (fun i => input_current_square M unit hunit M' unit' hunit' η hη i X)
    (fun i => input_backward_square M M' η i X)

end KTheory.Bass.SchemeModelRowSeed
