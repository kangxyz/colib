/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeExternalCells
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
variable {U : Scheme.{u}} (q : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

example (n : ℕ)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (laurent.op.obj X)))).space n) :
    ((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.target (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))) = Cell.target
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj ((baseProductFunctor
        q).op.obj X)))) n ((F.map (externalInverse (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) :=
  externalTransport_target_target q F X n x

example (n : ℕ) (t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))) = Cell.target
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        (Cell.overlap (F.mapArrow.mapArrow.obj (square (laurent.op.obj ((baseProductFunctor
        q).op.obj X)))) n t v ((F.map (baseProductSwapMap q (laurentProjection (.of (ULift.{u}
        ℤ))) X.unop).op).map n x)) :=
  externalTransport_target_overlap q F X n t v x

example (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) = Cell.upper
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) :=
  externalTransport_upper_lower q F X n r t x

example (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) = Cell.lower
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj ((baseProductFunctor
        q).op.obj X)))) n t ((F.map (externalInverse (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op).map n x)) :=
  externalTransport_lower_upper q F X n r t x

example (n : ℕ) (r s : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.target (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n (x))) = Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n ((F.map
        (baseProductSwapMap q (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).map n x)) :=
  externalTransport_overlap_target q F X n r s x

example (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj X)).space n) :
    ((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t v (x))) = Cell.overlap
        ((coneFunctor.obj F).mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        r s (Cell.overlap (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X))) n
        t v (x)) :=
  externalTransport_overlap_overlap q F X n r s t v x

end KTheory.Bass.GeometricConeInterchange
end
