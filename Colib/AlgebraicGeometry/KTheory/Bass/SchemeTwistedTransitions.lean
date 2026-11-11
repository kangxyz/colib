/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageSquare
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWords

/-! # The fixed geometric and loop words on normalized Scheme stages -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteLoopWords FiniteConeTopology GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The fixed loop reversal followed by the exact accumulated geometric word, including casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedTransitions.lean:27"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
def conjugatingIso (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    normalized squareFunctor i F ≅ normalized squareFunctor i F :=
  reversalIso i (iterate squareFunctor i F) ≪≫ (loopFunctor i).mapIso (wordAt i F)

/-- The normalized seed followed by the specified cyclic loop and geometric insertion words. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedTransitions.lean:32"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
def twistedTransition (A : Track laurent.op coefficient F) (i : ℕ) :
    normalized squareFunctor i F ⟶ normalized squareFunctor (i + 1) F :=
  normalizedTransition A i ≫ (cyclicIso i (iterate squareFunctor (i + 1) F)).hom ≫
    loopMap (i + 1) (betaAt i F).hom

/-- The stage isomorphism has precisely the prescribed execution order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedTransitions.lean:38"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
theorem conjugatingIso_hom (i : ℕ) :
    (conjugatingIso i F).hom =
      (reversalIso i (iterate squareFunctor i F)).hom ≫ loopMap i (wordAt i F).hom := rfl

end KTheory.Bass.SchemeNaturalSeed
