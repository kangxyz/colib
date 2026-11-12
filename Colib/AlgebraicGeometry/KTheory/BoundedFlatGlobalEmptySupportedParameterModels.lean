/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEmptySupportedModels
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterOpenTrack

/-!
# Empty-open support on the native scheme-parameter Waldhausen categories and Laurent tracks

The actual product open source has no points because its original second
projection maps to the empty fixed factor. Componentwise support-forgetful
Waldhausen isomorphisms assemble along the original pair pullbacks. Their forward
transformation is literally `ParameterModels.forget`; both directions preserve
the original projected Laurent unit and every time of its realized track.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterModels
open GlobalSectionChangeIndex GlobalSupportedParameter ParameterLaurentTrack ParameterLaurentUnit
open NaturalTrack

variable {P Q : Scheme.{u}} [IsEmpty P] (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual parameter open source is empty by its unchanged second projection. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:36"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
theorem parameterOpen_isEmpty (X : Scheme.{u}) : IsEmpty (pair f X).left :=
  Function.isEmpty (pullback.snd (specULiftZIsTerminal.from X) (specULiftZIsTerminal.from P))

/-- The original support-forgetful transformation is an isomorphism of parameter Waldhausen
categories. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:40"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
def emptySupportedIso : supported f ≅ ambient Q :=
  NatIso.ofComponents (fun X => by
    letI : IsEmpty ((𝟭 Scheme).obj (pair f X.unop).left) :=
      parameterOpen_isEmpty f X.unop
    exact emptySupportedModelIso (X := op (pair f X.unop).right)
      (pair f X.unop).hom)
    (fun g => (forget f).naturality g)

/-- The forward transformation retains the original support-forgetful Waldhausen arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:48"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
theorem emptySupportedIso_hom : (emptySupportedIso f).hom = forget f := rfl

/-- The original Laurent unit is preserved by the forward empty-support isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:51"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
theorem emptySupportedIso_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((emptySupportedIso f).hom.app (laurent.op.obj X)).hom.toFunctor
      (supportedUnit f X) (ambientUnit Q X) :=
  forget_unit f X

/-- Its literal inverse preserves the same projected Laurent unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:57"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
theorem emptySupportedIso_inv_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((emptySupportedIso f).inv.app (laurent.op.obj X)).hom.toFunctor
      (ambientUnit Q X) (supportedUnit f X) := by
  intro S
  apply ObjectProperty.hom_ext
  exact (map_lift_hom (parameterSupported f (laurent.op.obj X)).ι
    (ambientUnit Q X)
    (((emptySupportedIso f).inv.app (laurent.op.obj X)).hom.toFunctor.obj S)).symm

/-- The original whole Laurent track commutes with the forward parameter Waldhausen isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:67"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
theorem emptySupportedIso_equivariant :
    Equivariant (supportedTrack f) (ambientTrack Q)
      (Functor.whiskerRight (emptySupportedIso f).hom prespectrumFunctor) :=
  forget_equivariant f

/-- The literal inverse preserves every time of the same original Laurent track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalEmptySupportedParameterModels.lean:73"
  "adaptation" "Original parameter empty-support isomorphism and complete Laurent tracks."]
theorem emptySupportedIso_inv_equivariant :
    Equivariant (ambientTrack Q) (supportedTrack f)
      (Functor.whiskerRight (emptySupportedIso f).inv prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (emptySupportedIso_inv_unit f)

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterModels
