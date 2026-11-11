/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeExternalSquare
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
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (laurent.op.obj X))) n (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n (Cell.target (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))) :=
  permutation_external_target_target q F X n x

example (n : ℕ) (t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (laurent.op.obj X))) n t v (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))) :=
  permutation_external_target_overlap q F X n t v x

example (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) :=
  permutation_external_upper_lower q F X n r t x

example (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj X)).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t v (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square X)) n t v (x))) :=
  permutation_external_overlap_overlap q F X n r s t v x

example :
    (permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X =
      (externalTransport q F).app X ≫
        (permutation F ((baseProductFunctor q).op.obj X)).hom :=
  permutation_external_square q F X

example :
    (permutationNatIso ((baseProductFunctor q).op ⋙ F)).hom ≫ externalTransport q F =
      externalTransport q F ≫
        Functor.whiskerLeft (baseProductFunctor q).op (permutationNatIso F).hom :=
  permutation_external_naturality q F

end KTheory.Bass.GeometricConeInterchange
end
