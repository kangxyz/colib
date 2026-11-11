/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedLoop
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.Topology.Prespectrum.FiniteLoopWords

/-! # Original current-stage seed and normalized-stage compatibility

The whole original seed, independent loop times and literal association transports are
retained. This is the original equality of actual maps, not a stable-class replacement.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open FiniteParameterLooping IteratedLoopStrength FiniteLoopWords
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Every fixed-order loop strength retains the original seed with all its loop times. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedIterates.lean:28"
  "adaptation" "Original whole seed and fixed-order normalized transition square."]
theorem seed_iteratedStrength (A : Track laurent.op coefficient F) (j : ℕ) :
    seed (A.loops j) ≫ iteratedStrength squareFunctor j F = loopMap j (seed A) := by
  induction j with
  | zero => exact Category.comp_id _
  | succ j ih =>
    change seed (A.loops j).loop ≫
      (strengthDiagram squareFunctor _ ≫
        Functor.whiskerRight (iteratedStrength squareFunctor j F) parameterLoopingFunctor) =
      Functor.whiskerRight (loopMap j (seed A)) parameterLoopingFunctor
    rw [← Category.assoc, seed_loop_strength, ← Functor.whiskerRight_comp, ih]

end KTheory.Bass.SchemeNaturalSeed
