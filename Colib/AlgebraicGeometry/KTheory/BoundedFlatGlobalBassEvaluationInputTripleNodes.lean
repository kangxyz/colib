/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleSimplex
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNodeTransport

/-!
# The common reference for mixed global evaluation triple nodes

The original split-triple nodes are evaluated and anchored by the original total evaluation
comparison. The postcomposed evaluation chart retains its original first comparison.
Every node includes both its actual Model arrow and its full reference isomorphism.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputTripleNodes
open GlobalSectionChangeIndex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The original strict total pullback followed by evaluation. -/
def sourceMap :=
  boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g ≫ h).op ≫ evaluationModel (op X)

/-- A complete node referenced to the original strict total evaluation. -/
abbrev Node := Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op T) ⟶
    asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace),
  (sourceMap f g h).hom.toFunctor ≅ F.hom.toFunctor

/-- All eight original raw triple nodes, with the actual total evaluation reference. -/
def rawNode (i : Fin 8) : Node f g h :=
  ⟨evaluationModel (op T) ≫ BoundedFlatPerfectSplitTripleSimplex.vertices f g h i,
    evaluationComparisonIso (f ≫ g ≫ h) ≪≫
      isoWhiskerLeft (evaluationModel (op T)).hom.toFunctor
        (BoundedFlatPerfectSplitTripleSimplex.references f g h i)⟩

/-- All five original evaluation-chart nodes, postcomposed with actual raw pullback. -/
def postNode (i : Fin 5) : Node f g h :=
  ⟨InputSimplex.vertices g h i ≫ evaluationRawMap f,
    evaluationCompositionFirstIso f (g ≫ h) ≪≫
      isoWhiskerRight (InputSimplex.anchors g h i) (evaluationRawMap f).hom.toFunctor⟩

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputTripleNodes
