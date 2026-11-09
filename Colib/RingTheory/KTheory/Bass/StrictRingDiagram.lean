/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.KTheory.Bass.StrictDiagram

/-!
# The strict polynomial and Laurent Bass endofunctor

The actual coefficient inclusions and the two distinct Laurent charts specify the evaluation
square. The construction closes on strict spectrum-valued ring diagrams and their strict natural
transformations. A supplied seed arrow is iterated by this same endofunctor. The affine-section
application constructs its seed independently of the supplied-seed iteration.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u w
namespace KTheory.Bass

/-- Bass on strict ring diagrams, using the literal polynomial and Laurent coefficient square. -/
def strictRingDiagramFunctor :
    (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) ⥤ (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :=
  strictDiagramFunctor CommRingCat.PolynomialLaurent.laurentSquareFunctor

/-- Every iterate is again a strict ring diagram with an action on every coefficient map. -/
def strictRingDiagramIterate (n : ℕ) :
    (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) ⥤ (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :=
  strictDiagramIterate CommRingCat.PolynomialLaurent.laurentSquareFunctor n

/-- Apply the nth Bass endofunctor to the supplied seed, without introducing a new unit. -/
def strictRingDiagramTransition {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ strictRingDiagramFunctor.obj F) (n : ℕ) :
    (strictRingDiagramIterate n).obj F ⟶ (strictRingDiagramIterate (n + 1)).obj F :=
  strictDiagramTransition CommRingCat.PolynomialLaurent.laurentSquareFunctor η n

/-- The iterated original seed commutes literally with every coefficient map. -/
theorem strictRingDiagramTransition_naturality
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ strictRingDiagramFunctor.obj F) (n : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((strictRingDiagramIterate n).obj F).map f ≫
        (strictRingDiagramTransition η n).app S =
      (strictRingDiagramTransition η n).app R ≫
        ((strictRingDiagramIterate (n + 1)).obj F).map f :=
  (strictRingDiagramTransition η n).naturality f

end KTheory.Bass

attribute [colib_ref "quillen" "Quillen/KTheory/Bass/StrictRingDiagram.lean:25-50"
  "adaptation" "Actual two-chart Bass functor and formal finite iteration on ring diagrams"]
  KTheory.Bass.strictRingDiagramFunctor
  KTheory.Bass.strictRingDiagramIterate
  KTheory.Bass.strictRingDiagramTransition
  KTheory.Bass.strictRingDiagramTransition_naturality
