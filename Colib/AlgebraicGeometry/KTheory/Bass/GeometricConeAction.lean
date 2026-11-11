/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeExternalSquare
public import Colib.KTheory.Bass.ConeTrackDoubleTime

/-!
# The geometric double-cone permutation preserves the original whole action

The action is the existing `Track.cone` applied twice, including its original
inverse index maps and all endpoint casts. Its time slice is the actual twice
mapped original time slice followed by the two inverse interchanges in order.
The actual external-index square and ordinary diagram naturality prove full
same-time equivariance. No new action or coherence hypothesis is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
open NaturalTrack
variable {U : Scheme.{u}} (q : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track (baseProductFunctor q).op (NatTrans.op (baseProductProjection q)) F)

/-- The actual twice induced action keeps both inverse interchanges in their recursive order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeAction.lean:38"
  "adaptation" "Original same-time double action and actual whole permutation equivariance."]
theorem doubleCone_action_at (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (((A.cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q))
      squareFunctor (interchange q) (squareIso_projection q)).homotopy X).at r =
      (coneFunctor.map (coneFunctor.map
        (diagramHomotopyAt (η := (Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        F)) (θ := (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)) A.homotopy
        A.naturality r)) ≫ externalTransport q F).app X := by
  exact ConeTrackDoubleTime.doubleCone_action_at squareFunctor
    (baseProductFunctor q).op (NatTrans.op (baseProductProjection q))
    (interchange q) (squareIso_projection q) A X r

/-- The actual geometric permutation preserves the complete original twice induced action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeAction.lean:53"
  "adaptation" "Original same-time double action and actual whole permutation equivariance."]
theorem permutation_equivariant :
    Equivariant
      ((A.cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q))
      ((A.cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q))
      (permutationNatIso F).hom := by
  intro X r
  let h := diagramHomotopyAt
    (η := Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)
    (θ := Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)
    A.homotopy A.naturality r
  have hs : (permutation F X).hom ≫
      ((coneFunctor.map (coneFunctor.map h)).app X ≫ (externalTransport q F).app X) =
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (externalTransport q F).app X) ≫
      (permutation F ((baseProductFunctor q).op.obj X)).hom := by
    rw [← Category.assoc, ← permutation_diagram_naturality, Category.assoc,
      permutation_external_square, ← Category.assoc]
  exact (congrArg (fun k => (permutation F X).hom ≫ k)
    (doubleCone_action_at q A X r)).trans
      (hs.trans (congrArg (fun k => k ≫
        (permutation F ((baseProductFunctor q).op.obj X)).hom)
          (doubleCone_action_at q A X r).symm))

/-- Whole-time equivariance at every original point, with the action coordinate unchanged. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeAction.lean:84"
  "adaptation" "Original same-time double action and actual whole permutation equivariance."]
theorem permutation_action_apply (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((coneFunctor.obj (coneFunctor.obj F)).obj X).space n) :
    (((A.cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q))
      squareFunctor (interchange q) (squareIso_projection q)).homotopy X).level n
        (r, (permutation F X).hom.map n x) =
      (permutation F ((baseProductFunctor q).op.obj X)).hom.map n
        ((((A.cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (L := (baseProductFunctor q).op)
          (c := NatTrans.op (baseProductProjection q))
          squareFunctor (interchange q) (squareIso_projection q)).homotopy X).level n (r, x)) :=
  congrArg (fun k => k.map n x) (permutation_equivariant q A X r)

end KTheory.Bass.GeometricConeInterchange
