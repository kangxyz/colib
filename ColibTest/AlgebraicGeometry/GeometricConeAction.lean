/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWordAction
noncomputable section
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

example (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (((A.cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (L := (baseProductFunctor q).op)
      (c := NatTrans.op (baseProductProjection q))
      squareFunctor (interchange q) (squareIso_projection q)).homotopy X).at r =
      (coneFunctor.map (coneFunctor.map
        (diagramHomotopyAt (η := (Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        F)) (θ := (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)) A.homotopy
        A.naturality r)) ≫ externalTransport q F).app X :=
  doubleCone_action_at q A X r

example :
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
      (permutationNatIso F).hom :=
  permutation_equivariant q A

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
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
  permutation_action_apply q A X n r x

end KTheory.Bass.GeometricConeInterchange

namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange NaturalTrack
variable {U : Scheme.{u}} (q : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track (baseProductFunctor q).op (NatTrans.op (baseProductProjection q)) F)

example (i : ℕ) :
    Equivariant
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) (i + 1))
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) (i + 1))
      (betaAt i F).hom :=
  betaAt_equivariant q A i

example (i : ℕ) :
    Equivariant
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) i)
      (A.cones (L := (baseProductFunctor q).op)
        (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q) i)
      (wordAt i F).hom :=
  wordAt_equivariant q A i

end KTheory.Bass.GeometricConeFixedWords
end
