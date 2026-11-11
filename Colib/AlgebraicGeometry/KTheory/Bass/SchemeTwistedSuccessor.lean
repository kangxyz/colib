/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.FiniteTwistedTail
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeConeObjectIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNormalizedLoopInto
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeBetaRecursion

/-!
# The finite successor of the unchanged twisted Scheme transition

This local statement is conditional only on the displayed two-cone seed-rotation
equation. The geometric permutation, insertion word, and twisted transition are the
previously fixed actual maps. It does not assert that the geometric input has been proved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology IteratedLoopStrength FiniteLoopWords
open AssociatedStrength FiniteTwistedTail
open GeometricConeInterchange GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- One actual two-cone rotation equation gives the successor square for the fixed transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTwistedSuccessor.lean:36"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem twistedTransition_successor (A : Track laurent.op coefficient F) (i : ℕ)
    (h : (strictDiagramFunctor squareFunctor).map (seed (coneTrack A i)) ≫
        strengthDiagram squareFunctor (iterate squareFunctor (i + 1) F) =
      Functor.whiskerRight (seed (coneTrack A (i + 1))) parameterLoopingFunctor ≫
        (transposeIso (iterate squareFunctor (i + 2) F)).inv ≫
        loopMap 2 (permutationNatIso (iterate squareFunctor i F)).hom) :
    (strictDiagramFunctor squareFunctor).map (twistedTransition A i) ≫
        associatedStrength squareFunctor (i + 1) (iterate squareFunctor (i + 1) F) =
      associatedStrength squareFunctor i (iterate squareFunctor i F) ≫
        twistedTransition A (i + 1) := by
  have hb := (betaAt_succ_hom i F).symm
  have hf := finite_twisted_rotation_of_tail squareFunctor i (iterate squareFunctor i F)
    (seed (coneTrack A i)) (seed (coneTrack A (i + 1)))
    (permutationNatIso (iterate squareFunctor i F)).hom (betaAt i F).hom
    (betaAt (i + 1) F).hom h (by
      dsimp only [coneFunctor_obj_eq, iterate] at hb ⊢
      exact hb)
  simp only [twistedTransition, normalizedTransition_loopInto]
  dsimp only [NormalizedStageMap.normalized, iterate, coneFunctor_obj_eq] at hf ⊢
  exact hf

end KTheory.Bass.SchemeIteratedSeedTransition
