/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedNull

/-! # The actual original iterated-seed comparison preserves input maps and whole nulls -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTelescope
open NaturalTrack GeometricSeedCospan NormalizedStageMap SchemeNaturalSeed
variable {F G K : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The actual original-to-twisted comparison commutes with each equivariant input map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedNullComparison.lean:25"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem input_square (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    iteratedInputMap A B η hη ≫ iteratedTwistedTelescopeMap B =
      iteratedTwistedTelescopeMap A ≫ twistedInputMap A B η hη := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i s x
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (normalized squareFunctor j G).obj X)
    (fun j => (twistedTransition B j).app X) n i (s, y))
    (congrArg (fun t => (t.app X).map n x) (stageMap_naturality squareFunctor i η))

/-- Every original null time survives the actual original-to-twisted telescope map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeIteratedSeedNullComparison.lean:39"
  "adaptation" "Original geometric seed rotation and iterated-to-twisted whole-null bridge."]
theorem null_square (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (D : Track laurent.op coefficient K)
    (a : F ⟶ G) (b : G ⟶ K) (ha : Equivariant A B a) (hb : Equivariant B D b)
    (N : DiagramNullHomotopy a b)
    (hN : ∀ r, Equivariant A D
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r))
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((iteratedTelescope A).obj X).space n) :
    ((iteratedTwistedTelescopeMap D).app X).map n
      (((iteratedInputNull A B D a b ha hb N hN).homotopy X).level n (r, x)) =
      ((twistedInputNull A B D a b ha hb N hN).homotopy X).level n
        (r, ((iteratedTwistedTelescopeMap A).app X).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun i => (normalized squareFunctor i K).obj X)
      (fun i => (twistedTransition D i).app X) n z.1 (z.2.1, y))
      (stageMap_null squareFunctor N z.1 X n r z.2.2)

end KTheory.Bass.SchemeIteratedSeedTelescope
