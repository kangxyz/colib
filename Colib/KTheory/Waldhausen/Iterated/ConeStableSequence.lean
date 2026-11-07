/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Iterated.ConeFiberExcision
public import Colib.Topology.Prespectrum.ConeStableNaturality

/-!
# Unconditional original stable cone sequences for actual S-models

The genuine original cone-to-fiber theorem discharges the excision premise of the signed cone
sequence for every map between actual S-models. It likewise discharges both row premises for
stable comparison of their literal mapping cones under an unchanged strict arrow square.
-/

/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/ConeStableSequence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS

open Topology SmallWaldhausenCategory

/-- The actual original S-map boundary has all three recurring signed exactness positions. -/
theorem prespectrum_stableMappingConeLongExactSequence {W V : WideSubcategory preservesZero.{u}}
    (f : prespectrum W ⟶ prespectrum V) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f))
      (stableMappingConeConnecting f (prespectrum_mappingConeFiberComparison_isStableEquivalence f)
        d) ∧
    Function.Exact
      (stableMappingConeConnecting f (prespectrum_mappingConeFiberComparison_isStableEquivalence f)
        d) ((stableHomotopyFunctor d).map f) ∧
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  stableMappingConeLongExactSequence f
    (prespectrum_mappingConeFiberComparison_isStableEquivalence f) d

/-- Stable original sides preserve the literal mapping cone of maps between actual S-models. -/
theorem prespectrum_mappingConeMap_isStableEquivalence
    {W V W' V' : WideSubcategory preservesZero.{u}}
    {f : prespectrum W ⟶ prespectrum V} {g : prespectrum W' ⟶ prespectrum V'}
    (sq : Arrow.mk f ⟶ Arrow.mk g)
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_excision sq
    (prespectrum_mappingConeFiberComparison_isStableEquivalence f)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence g) hl hr

/-- The original model with independent object and morphism universes has an exact
target/cone pair. -/
theorem originalPrespectrum_stableMappingCone_exact_target
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V)
    (d : ℤ) : Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  stableMappingCone_exact_target f
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence W V f) d

end CategoryTheory.Waldhausen.IteratedS
