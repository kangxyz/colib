/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationStrictSeed

/-! # Naturality on the actual strict side of the global Bass seed comparison -/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedWords

/-- The original strict one-step map induced by the actual scheme arrow. -/
def strictInput {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (((KTheory.Bass.strictDiagramFunctor squareFunctor).obj sectionDiagram).map g.op)

private theorem naturality_of_components {D : Type*} [Category D]
    {A B C E : D} (f : A ⟶ B) (g : C ⟶ E)
    {sB tB : B ⟶ E} {sA tA : A ⟶ C}
    (hB : sB = tB) (hA : sA = tA) (h : f ≫ tB = tA ≫ g) :
    f ≫ sB = sA ≫ g := by
  rw [hB, hA, h]

set_option maxHeartbeats 800000 in
-- Checking the specialized square compares the actual section and strict diagram maps.
/-- The actual forward strict seed is natural, with its prescribed whole unit-and-null word. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedWords.lean"
  "adaptation" "The literal source natural transformation for the original seed routes"]
theorem strict_seed_naturality {X Y : Scheme.{u}} (g : X ⟶ Y) :
    sectionMap g ≫ strictSeed X = strictSeed Y ≫ strictInput g := by
  have h := (KTheory.Bass.WholeSeedCospan.seed
    (KTheory.Bass.GeometricSquareInterchange.geometricSquare sectionDiagram)
    (KTheory.Bass.GeometricSeedCospan.sourceTrack sectionDiagram strictLaurentTrack)
    (KTheory.Bass.GeometricSeedCospan.sourceTrack_naturality sectionDiagram
      strictLaurentTrack strictLaurentTrack_naturality)).naturality g.op
  have hX := strictSeed_eq_wholeSeed X
  have hY := strictSeed_eq_wholeSeed Y
  exact naturality_of_components _ _ hX hY h

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedWords
