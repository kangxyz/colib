/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.RingTheory.KTheory.Bass.StrictRingDiagram
public import Colib.CategoryTheory.Functor.ArrowSquareWhiskering

/-!
# Restricting the original strict Bass diagrams to algebras over a fixed ring

The original Laurent square over Under R forgets to the same ring square. Restriction
therefore commutes with the actual Bass endofunctor. The seed construction
retains the original natural arrow, using only the specified functor equality at its target.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u w
namespace KTheory.Bass

/-- Restriction of an original ring diagram along the literal Under.forget functor. -/
def strictRingDiagramRestriction (R : CommRingCat.{u}) :
    (CommRingCat.{u} ⥤ LoopPrespectrum.{w}) ⥤ (Under R ⥤ LoopPrespectrum.{w}) :=
  (Functor.whiskeringLeft (Under R) CommRingCat LoopPrespectrum).obj (Under.forget R)

/-- Restricting original Laurent squares commutes literally with the same cone-loop functor. -/
theorem strictRingDiagramRestriction_comp_bass (R : CommRingCat.{u}) :
    strictRingDiagramRestriction.{u,w} R ⋙
        strictDiagramFunctor (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R) =
      strictRingDiagramFunctor ⋙ strictRingDiagramRestriction R := by
  unfold strictRingDiagramRestriction strictRingDiagramFunctor strictDiagramFunctor
  exact Functor.whiskeringLeft_comp_mapArrowSquare
    (Under.forget R)
    (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R)
    CommRingCat.PolynomialLaurent.laurentSquareFunctor
    LoopPrespectrum.strictSquareLoopedConeFunctor
    (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor_comp_forget R)

/-- The restricted original seed retains the given arrow and only its proved endpoint equality. -/
def strictRingDiagramUnderSeed (R : CommRingCat.{u})
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}} (η : F ⟶ strictRingDiagramFunctor.obj F) :
    Under.forget R ⋙ F ⟶
      (strictDiagramFunctor (CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor R)).obj
        (Under.forget R ⋙ F) :=
  (strictRingDiagramRestriction R).map η ≫
    eqToHom (congrArg (fun H ↦ H.obj F) (strictRingDiagramRestriction_comp_bass R).symm)

attribute [local irreducible] LoopPrespectrum.strictSquareLoopedConeFunctor

/-- The actual component of the restricted seed is the unchanged original ring component. -/
theorem strictRingDiagramUnderSeed_app (R : CommRingCat.{u})
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}} (η : F ⟶ strictRingDiagramFunctor.obj F)
    (a : Under R) : (strictRingDiagramUnderSeed R η).app a = η.app a.right := rfl

attribute [colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictUnderDiagram.lean:25-33,51-62"
  "adaptation" "Literal fixed-base restriction of the native strict Laurent diagram and seed"]
  strictRingDiagramRestriction
  strictRingDiagramRestriction_comp_bass
  strictRingDiagramUnderSeed
  strictRingDiagramUnderSeed_app

end KTheory.Bass
