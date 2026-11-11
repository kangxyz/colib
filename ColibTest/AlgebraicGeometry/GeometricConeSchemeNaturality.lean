/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})



example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ)
    (z : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) :=
  permutation_scheme_target_target F g n z

example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (t v :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) :=
  permutation_scheme_target_overlap F g n t v z

example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r s t v :
        unitInterval)
    (z : (F.obj X).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) :=
  permutation_scheme_overlap_overlap F g n r s t v z

example {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    (coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom =
      (permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g :=
  permutation_scheme_naturality F g

example : coneFunctor.obj (coneFunctor.obj F) ≅
    coneFunctor.obj (coneFunctor.obj F) :=
  permutationNatIso F

example : coneFunctor.{u,w} ⋙ coneFunctor ≅ coneFunctor ⋙ coneFunctor :=
  permutationFunctorIso

end KTheory.Bass.GeometricConeInterchange
end
