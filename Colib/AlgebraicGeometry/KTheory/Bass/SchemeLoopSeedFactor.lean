/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedLoop
public import Colib.KTheory.Bass.LoopStable

/-! # The original loop-seed factor with the inverse transpose retained -/
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
open LoopFactor
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Removing the original strength's final transpose retains its specified inverse. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeLoopSeedFactor.lean:25"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem seed_loop_coneStrength (A : Track laurent.op coefficient F) (X : Scheme.{u}ᵒᵖ) :
    (seed A.loop).app X ≫ parameterLoopingMap
        (coneStrength (F.mapArrow.mapArrow.obj (squareFunctor.obj X))) =
      parameterLoopingMap ((seed A).app X) ≫
        (LoopTranspose.iso ((ConeTrack.diagram squareFunctor F).obj X)).inv := by
  apply (cancel_mono (LoopTranspose.iso
    ((ConeTrack.diagram squareFunctor F).obj X)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hf := LoopStable.strength_factor squareFunctor F X
  exact (congrArg (fun k => (seed A.loop).app X ≫ k) hf.symm).trans
    (congrArg (fun k => k.app X) (seed_loop_strength A))

end KTheory.Bass.SchemeIteratedSeedTransition
