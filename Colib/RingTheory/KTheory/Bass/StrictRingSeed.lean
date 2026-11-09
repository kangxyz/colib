/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.RingTheory.KTheory.Bass.StrictRingDiagram

/-! Assemble pointwise maps into the existing strict Bass endofunctor without changing their values.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u w
namespace KTheory.Bass

/-- The exact cone-loop coefficient squares assemble the same supplied pointwise maps. -/
def strictRingDiagramSeed (F : CommRingCat.{u} ⥤ LoopPrespectrum.{w})
    (η : ∀ R, F.obj R ⟶ parameterLooping (mappingCone
      (StrictSquare.comparison (F.mapArrow.mapArrow.obj (laurentSquare R)))))
    (hη : ∀ {R S} (f : R ⟶ S), η R ≫ parameterLoopingMap
      (mappingConeMap (strictSquareComparisonFunctor.map
        (F.mapArrow.mapArrow.map (laurentSquareMap f)))) = F.map f ≫ η S) :
    F ⟶ strictRingDiagramFunctor.obj F where
  app := η
  naturality _ _ f := (hη f).symm

/-- Evaluation of the assembled natural transformation keeps its original pointwise map. -/
theorem strictRingDiagramSeed_app (F : CommRingCat.{u} ⥤ LoopPrespectrum.{w})
    (η : ∀ R, F.obj R ⟶ parameterLooping (mappingCone
      (StrictSquare.comparison (F.mapArrow.mapArrow.obj (laurentSquare R)))))
    (hη : ∀ {R S} (f : R ⟶ S), η R ≫ parameterLoopingMap
      (mappingConeMap (strictSquareComparisonFunctor.map
        (F.mapArrow.mapArrow.map (laurentSquareMap f)))) = F.map f ≫ η S) (R : CommRingCat.{u}) :
    (strictRingDiagramSeed F η hη).app R = η R := rfl

end KTheory.Bass
