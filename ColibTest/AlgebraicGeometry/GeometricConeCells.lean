/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeCells
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

example (n : ℕ)
    (x : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))) =
      Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n ((F.map (baseProductSwapMap
        (laurentProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) :=
  permutation_target_target F X n x

example (n : ℕ) (t v : unitInterval)
    (x : (F.obj (laurent.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))) =
      Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (x)) :=
  permutation_target_overlap F X n t v x

example (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) =
      Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) :=
  permutation_upper_lower F X n r t x

example (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) =
      Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) :=
  permutation_lower_upper F X n r t x

example (n : ℕ) (r s : unitInterval)
    (x : (F.obj (laurent.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (x))) =
      Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r s (x)) :=
  permutation_overlap_target F X n r s x

example (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj X).space n) :
    (permutation F X).hom.map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (x))) =
      Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n r s (x)) :=
  permutation_overlap_overlap F X n r s t v x

end KTheory.Bass.GeometricConeInterchange
end
