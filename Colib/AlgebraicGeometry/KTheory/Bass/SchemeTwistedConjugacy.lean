/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedAdjacent
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWordAction

/-! # Actual fixed-word seed equivariance and normalized conjugacy -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The actual accumulated cone permutation preserves its original local seed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedConjugacy.lean:25"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
theorem wordAt_seed_square (A : Track laurent.op coefficient F) (i : ℕ) :
    seed (coneTrack A i) ≫ (strictDiagramFunctor squareFunctor).map (wordAt i F).hom =
      (wordAt i F).hom ≫ seed (coneTrack A i) :=
  seed_square (coneTrack A i) (coneTrack A i) (wordAt i F).hom
    (wordAt_equivariant (laurentProjection (.of (ULift.{u} ℤ))) A i)

/-- The prescribed reversal and cone word conjugate the actual adjacent transitions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedConjugacy.lean:32"
  "adaptation" "Original actual fixed-word conjugacy and whole-height telescope comparison."]
theorem twisted_adjacent (A : Track laurent.op coefficient F) (i : ℕ) :
    normalizedTransition A i ≫ (conjugatingIso (i + 1) F).hom =
      (conjugatingIso i F).hom ≫ twistedTransition A i :=
  twisted_adjacent_of_seed_square A i (wordAt_seed_square A i)

end KTheory.Bass.SchemeNaturalSeed
