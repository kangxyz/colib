/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationSourceLeg
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSectionUnit
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality

/-! # The chosen forward Laurent unit and the strict global Bass seed -/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CategoryTheory.Functor.IdentityAutomorphism CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open KTheory.Bass.GeometricSeedCospan
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation

/-- The actual evaluation-lifted Laurent unit on the strict global section model. -/
def strictLaurentUnit (X : Scheme.{u}ᵒᵖ) :=
  boundedAboveFlatGlobalSectionUnit (laurent.op.obj X) (laurentScalar X)

/-- The chosen unit is preserved by every literal scheme reindexing. -/
theorem strictLaurentUnit_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Preserves (boundedAboveFlatGlobalSectionModelFunctor.map (laurent.op.map f)).hom.toFunctor
      (strictLaurentUnit X) (strictLaurentUnit Y) :=
  boundedAboveFlatGlobalSectionUnit_reindex_of_eq (laurent.op.map f)
    (laurentScalar X) (laurentScalar Y) (laurentScalar_map f)

/-- Realize the forward unit along the same Laurent projection in the actual diagram. -/
def strictLaurentTrack (X : Scheme.{u}ᵒᵖ) :
    Homotopy (sectionDiagram.map (coefficient.app X)) (sectionDiagram.map (coefficient.app X)) :=
  prespectrumIsoHomotopy (boundedAboveFlatGlobalSectionModelFunctor.map (coefficient.app X))
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficient.app X)).hom.toFunctor
      (strictLaurentUnit X))

/-- Every time of the actual unit track commutes with literal scheme reindexing. -/
theorem strictLaurentTrack_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (r : unitInterval) (x : (sectionDiagram.obj X).space n) :
    (sectionDiagram.map (laurent.op.map f)).map n ((strictLaurentTrack X).level n (r, x)) =
      (strictLaurentTrack Y).level n (r, (sectionDiagram.map f).map n x) := by
  have h : boundedAboveFlatGlobalSectionModelFunctor.map (coefficient.app X) ≫
      boundedAboveFlatGlobalSectionModelFunctor.map (laurent.op.map f) =
      boundedAboveFlatGlobalSectionModelFunctor.map f ≫
        boundedAboveFlatGlobalSectionModelFunctor.map (coefficient.app Y) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg boundedAboveFlatGlobalSectionModelFunctor.map
      (coefficient.naturality f).symm
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h))
      (strictLaurentUnit X) (strictLaurentUnit Y) (strictLaurentUnit_naturality f).whisker) n r x

/-- Use the actual strict source-null cylinder and no substitute seed. -/
def strictSeed (X : Scheme.{u}) : sectionDiagram.obj (op X) ⟶
    parameterLooping (mappingCone (StrictSquare.comparison (sectionSquare X))) :=
  ((strictLaurentTrack (op X)).postcomp
    (mappingConeInclusion (StrictSquare.comparison (sectionSquare X)))).nullLoopMap
      (strictSourceNull X)

/-- This seed is literally the existing whole-word geometric seed with the chosen track. -/
theorem strictSeed_eq_wholeSeed (X : Scheme.{u}) :
    strictSeed X =
      (KTheory.Bass.WholeSeedCospan.seed
        (KTheory.Bass.GeometricSquareInterchange.geometricSquare sectionDiagram)
        (KTheory.Bass.GeometricSeedCospan.sourceTrack sectionDiagram strictLaurentTrack)
        (KTheory.Bass.GeometricSeedCospan.sourceTrack_naturality sectionDiagram strictLaurentTrack
          strictLaurentTrack_naturality)).app (op X) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation
