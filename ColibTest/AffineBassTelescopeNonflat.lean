/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassStableColimit
import Mathlib.Data.ZMod.Basic

/-! The actual nonflat, noninjective coefficient map from the integers to ZMod 2. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

private abbrev modTwo : CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (Int.castRingHom (ZMod 2))

example (n : ℕ) : (boundedAboveFlatAffineSectionBassDiagram n).map modTwo ≫
      (boundedAboveFlatAffineSectionBassTransition n).app (.of (ZMod 2)) =
    (boundedAboveFlatAffineSectionBassTransition n).app (.of ℤ) ≫
      (boundedAboveFlatAffineSectionBassDiagram (n + 1)).map modTwo :=
  boundedAboveFlatAffineSectionBassTransition_naturality n modTwo

example (d : ℤ) :
    colimMap (boundedAboveFlatAffineSectionBassStableDiagramMap modTwo d) ≫
      (boundedAboveFlatAffineSectionBassStableColimitIso (.of (ZMod 2)) d).hom =
    (boundedAboveFlatAffineSectionBassStableColimitIso (.of ℤ) d).hom ≫
      (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap modTwo) :=
  boundedAboveFlatAffineSectionBassStableColimitIso_naturality modTwo d

example (i k : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj (.of ℤ)).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeMap modTwo).map k
      ((boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy (.of ℤ) i).level k (s, x)) =
    (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy (.of (ZMod 2)) i).level k
      (s, ((boundedAboveFlatAffineSectionBassDiagram i).map modTwo).map k x) :=
  Telescope.diagramInclusionHomotopy_naturality_apply _ _ modTwo i k s x
