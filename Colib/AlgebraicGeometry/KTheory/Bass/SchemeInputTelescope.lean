/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputTransition

/-! # Naturality of the actual current-stage telescope comparison in its input

A single local whole-time action square supplies the actual maps of both
original towers. Their comparison commutes on the entire telescope, retaining
every cylinder height and the original finite-stage normalization maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (η : F ⟶ G) (hη : Equivariant A B η)

/-- The original finite Bass images induce the actual current-seed telescope input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTelescope.lean:33"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
def currentInputMap : currentTelescope A ⟶ currentTelescope B :=
  Telescope.diagramMap (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (fun i => (strictDiagramIterate squareFunctor i).obj G)
    (currentTransition A) (currentTransition B)
    (fun i => (strictDiagramIterate squareFunctor i).map η)
    (currentInput_transition A B η hη)

/-- The original finite looped cone maps induce the unpermuted normalized telescope input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTelescope.lean:41"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
def normalizedInputMap : normalizedTelescope A ⟶ normalizedTelescope B :=
  Telescope.diagramMap (fun i => normalized squareFunctor i F)
    (fun i => normalized squareFunctor i G) (normalizedTransition A) (normalizedTransition B)
    (fun i => normalizedMap squareFunctor i η) (normalizedInput_transition A B η hη)

/-- The current input map retains the whole original cylinder and its height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTelescope.lean:47"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem currentInputMap_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((currentInputMap A B η hη).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (currentTransition A j).app X) n i (s, x)) =
      Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj G).obj X)
        (fun j => (currentTransition B j).app X) n i
        (s, (((strictDiagramIterate squareFunctor i).map η).app X).map n x) := rfl

/-- The normalized input map likewise keeps its original cylinder height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTelescope.lean:57"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem normalizedInputMap_cylinder (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : ((normalized squareFunctor i F).obj X).space n) :
    ((normalizedInputMap A B η hη).app X).map n
      (Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (normalizedTransition A j).app X) n i (s, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
        (fun j => (normalizedTransition B j).app X) n i
        (s, ((normalizedMap squareFunctor i η).app X).map n x) := rfl

/-- The unchanged telescope comparison commutes with every actual equivariant input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInputTelescope.lean:67"
  "adaptation" "Original whole equivariance and current/normalized telescope input maps."]
theorem telescopeMap_input_square :
    currentInputMap A B η hη ≫ telescopeMap B =
      telescopeMap A ≫ normalizedInputMap A B η hη := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i s x
  change Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
      (fun j => (normalizedTransition B j).app X) n i
      (s, ((stageMap squareFunctor i G).app X).map n
        ((((strictDiagramIterate squareFunctor i).map η).app X).map n x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
      (fun j => (normalizedTransition B j).app X) n i
      (s, ((normalizedMap squareFunctor i η).app X).map n
        (((stageMap squareFunctor i F).app X).map n x))
  exact congrArg (fun y => Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
    (fun j => (normalizedTransition B j).app X) n i (s, y))
      (congrArg (fun t => (t.app X).map n x) (stageMap_naturality squareFunctor i η))

end KTheory.Bass.SchemeNaturalSeed
