/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeTarget
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u w
namespace KTheory.Bass.GeometricConeInterchange

variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
open GeometricSquareInterchange
example : geometricSquare (coneFunctor.obj F) ≅
    coneFunctor.mapArrow.mapArrow.obj (geometricSquare F) :=
  squareInterchange F

example (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow LoopPrespectrum.{w}) :=
  componentTarget F X

example (X : Scheme.{u}ᵒᵖ) : target F X ≅ componentTarget F X :=
  targetComponentIso F X

example (X : Scheme.{u}ᵒᵖ) :
    (coneFunctor.obj F).mapArrow.mapArrow.obj (square X) ≅ target F X :=
  targetIso F X

example (X : Scheme.{u}ᵒᵖ) :
    (coneFunctor.obj (coneFunctor.obj F)).obj X ≅ (coneFunctor.obj (coneFunctor.obj F)).obj X :=
  permutation F X

end KTheory.Bass.GeometricConeInterchange
end
