/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.LoopStrength
public import Colib.Topology.Prespectrum.LoopTranspose

/-!
# The fixed-order finite iteration of the original loop strength

The original strength components give an actual natural transformation. Its iteration uses
`kappa_(Omega^j G)` first and then `Omega(kappa^j_G)`, without changing the original transpose
or choosing another comparison. This file contains the original definitions and naturality
proof only; the stability theorem for genuine finite normalized Model stages is deferred.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.IteratedLoopStrength
open LoopStrength
variable {C : Type u} [Category.{v} C]

/-- The original pointwise strength is natural in the coefficient index. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedLoopStrength.lean:29"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def strengthDiagram (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor) ⟶
      (strictDiagramFunctor Q).obj F ⋙ parameterLoopingFunctor where
  app := strength Q F
  naturality {X Y} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    apply Path.ext
    funext r
    exact (strictDiagramMapHomotopy_naturality
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F) (evaluation F)
      (evaluation_naturality F) Q f n r x).symm

/-- Cross the outermost loop first, then loop the previously fixed comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedLoopStrength.lean:46"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def iteratedStrength (Q : C ⥤ Arrow (Arrow C)) :
    ∀ (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
      (strictDiagramFunctor Q).obj (loopDiagram j F) ⟶
        loopDiagram j ((strictDiagramFunctor Q).obj F)
  | 0, F => 𝟙 ((strictDiagramFunctor Q).obj F)
  | j + 1, F => strengthDiagram Q (loopDiagram j F) ≫
      Functor.whiskerRight (iteratedStrength Q j F) parameterLoopingFunctor


end KTheory.Bass.IteratedLoopStrength
