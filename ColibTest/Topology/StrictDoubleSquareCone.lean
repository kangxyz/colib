/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.StrictDoubleSquareCone
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
example : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u} := totalFunctor
namespace Double
variable (E : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{u}))))

example (K : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u}) :
    HomotopyPushout.prespectrum (K.map E.left.hom) (K.map E.hom.left) ⟶ K.obj E.right.right :=
  cornerComparison E K

example
    {K L : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u}} (e : K ⟶ L) :
    HomotopyPushout.map (K.map E.left.hom) (K.map E.hom.left)
        (L.map E.left.hom) (L.map E.hom.left)
        (e.app E.left.left) (e.app E.left.right) (e.app E.right.left)
        (e.naturality E.left.hom) (e.naturality E.hom.left) ≫ cornerComparison E L =
      cornerComparison E K ≫ e.app E.right.right :=
  cornerComparison_naturality E e

example : Pushout.square E.left.hom E.hom.left ⟶ E.right.right :=
  comparisonMap E

example :
    (Pushout.totalIso E.left.hom E.hom.left).hom ≫ totalFunctor.map (comparisonMap E) =
      comparison (totalFunctor.mapArrow.mapArrow.obj E) :=
  sourceIso_comparison E

example : totalFunctor.obj (totalFunctor.mapArrow.mapArrow.obj E) ≅
    totalFunctor.obj (coneSquare (comparisonMap E)) :=
  interchangeIso E

end Double
end Topology.LoopPrespectrum.StrictSquare
end
