/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeNaturality
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}


example (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (z : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) :=
  permutation_diagram_target_target h X n z

example (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t v :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) :=
  permutation_diagram_target_overlap h X n t v z

example (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) :=
  permutation_diagram_upper_lower h X n r t z

example (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (z))) :=
  permutation_diagram_overlap_target h X n r s z

example (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t v :
        unitInterval)
    (z : (F.obj X).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) :=
  permutation_diagram_overlap_overlap h X n r s t v z

example (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) :
    (coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom =
      (permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X :=
  permutation_diagram_naturality h X

end KTheory.Bass.GeometricConeInterchange
end
