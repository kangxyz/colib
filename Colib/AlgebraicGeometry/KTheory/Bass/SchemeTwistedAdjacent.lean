/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNormalizedLoopInto
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWordRecursion

/-! # The fixed normalized conjugacy from its one local seed square -/
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
open NaturalTrack GeometricSeedCospan
open FiniteLoopConjugacy FiniteConeTopology GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- One actual local seed-equivariance square gives the exact adjacent fixed-word conjugacy. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedAdjacent.lean:27"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
theorem twisted_adjacent_of_seed_square (A : Track laurent.op coefficient F) (i : ℕ)
    (h : seed (coneTrack A i) ≫ (strictDiagramFunctor squareFunctor).map (wordAt i F).hom =
      (wordAt i F).hom ≫ seed (coneTrack A i)) :
    normalizedTransition A i ≫ (conjugatingIso (i + 1) F).hom =
      (conjugatingIso i F).hom ≫ twistedTransition A i := by
  have hs := loopInto_conjugacy i
    (A := iterate squareFunctor i F) (B := iterate squareFunctor (i + 1) F)
    (seed (coneTrack A i)) (wordAt i F).hom
    (ConeTrack.map squareFunctor (wordAt i F).hom) (betaAt i F).hom h
  simpa only [conjugatingIso_hom, twistedTransition, normalizedTransition_loopInto,
    wordAt_succ_hom, Category.assoc] using hs

end KTheory.Bass.SchemeNaturalSeed
