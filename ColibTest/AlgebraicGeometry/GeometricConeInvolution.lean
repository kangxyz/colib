/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeInvolution
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n (Cell.target (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n (x)))) = Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))
        :=
  permutation_twice_target_target F X n x

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = Cell.upper ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)) :=
  permutation_twice_upper_upper F X n r t x

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = Cell.lower ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)) :=
  permutation_twice_lower_lower F X n r t x

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj X).space n) :
    (permutation F X).hom.map n ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj
        F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj
        (square X)) n t v (x)))) = Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj (square X)) n t v (x)) :=
  permutation_twice_overlap_overlap F X n r s t v x

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (permutation F X).hom ≫ (permutation F X).hom = 𝟙 _ :=
  permutation_comp F X

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (permutation F X).inv = (permutation F X).hom :=
  permutation_inv_eq_hom F X

end KTheory.Bass.GeometricConeInterchange
end
