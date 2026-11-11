/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalOpenPairDiagram

/-! # Original Laurent tracks under change of weakness and actual open restriction -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open GlobalSupportedSection ParameterLaurentUnit NaturalTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

private theorem preservesIdentity {C : Type*} [Category C] (α : 𝟭 C ≅ 𝟭 C) :
    Preserves (𝟭 C) α α := fun _ => rfl

/-- The relative-open category retains the original ambient identity unit unchanged. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:87"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
def openUnit (X : Scheme.{u}ᵒᵖ) :
    𝟭 ((ParameterModels.openModel f).obj (laurent.op.obj X)).obj.Obj ≅
      𝟭 ((ParameterModels.openModel f).obj (laurent.op.obj X)).obj.Obj := ambientUnit Q X

/-- The actual relative-open reindexing preserves the same projected parameter unit. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:92"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
theorem openUnit_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.openModel f).map (laurent.op.map g)).hom.toFunctor
      (openUnit f X) (openUnit f Y) := by
  exact ambientUnit_naturality Q g

/-- The original relative-open whole parameter track. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:98"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
def openTrack :
    Track laurent.op coefficient (ParameterModels.openModel f ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.openModel f)
    (openUnit f) (openUnit_naturality f)

/-- The identity change of weak class preserves the original unit literally. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:114"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
theorem changeWeak_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.changeWeak f).app (laurent.op.obj X)).hom.toFunctor
      (ambientUnit Q X) (openUnit f X) := by
  exact preservesIdentity (ambientUnit Q X)

/-- Geometric open restriction preserves the same external parameter Laurent coordinate. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:120"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
theorem openRestriction_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.openRestriction f).app (laurent.op.obj X)).hom.toFunctor
      (openUnit f X) (ambientUnit P X) := ambientUnit_factor f X

/-- The original change of weakness preserves every scalar-track time. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:131"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
theorem changeWeak_equivariant :
    Equivariant (ambientTrack Q) (openTrack f)
      (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (changeWeak_unit f)

/-- The original geometric restriction preserves every scalar-track time. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:137"
  "adaptation" "Original unchanged unit and complete-time restriction track."]
theorem openRestriction_equivariant :
    Equivariant (openTrack f) (ambientTrack P)
      (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (openRestriction_unit f)

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack

namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack

attribute [colib_tag "COL-0541"] openRestriction_equivariant
attribute [colib_tag "COL-0541"] openTrack
attribute [colib_tag "COL-0541"] changeWeak_equivariant

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
