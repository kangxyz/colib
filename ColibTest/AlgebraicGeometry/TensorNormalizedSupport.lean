/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorNormalizedTrack
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.Test0
example (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    normalizedTensorUnit X r = boundedAboveFlatPerfectGlobalUnitIso X r :=
  GlobalSectionChangeIndex.normalizedTensorUnit_eq X r
end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.Test0

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.Test1
example (X : Scheme.{u}ᵒᵖ)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSectionEvaluation X) (globalNormalizedTensorUnit X r)
      (normalizedTensorUnit X.unop r) :=
  GlobalSectionChangeIndex.globalNormalizedTensorUnit_evaluation X r
end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.Test1

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.Test2
example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSectionModelFunctor.map f).hom.toFunctor
      (globalNormalizedTensorUnit X r)
      (globalNormalizedTensorUnit Y (Units.map f.unop.appTop.hom.toMonoidHom r)) :=
  GlobalSectionChangeIndex.globalNormalizedTensorUnit_reindex f r
end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.Test2

namespace AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.Test3
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack
example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ambientUnit Q X = ParameterLaurentUnit.ambientUnit Q X :=
  GlobalTensorNormalizedSupport.ambientUnit_eq Q X
end AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.Test3

namespace AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.Test4
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
example (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.forget f).app (laurent.op.obj X)).hom.toFunctor
      (supportedUnit f X) (ambientUnit Q X) :=
  GlobalTensorNormalizedSupport.forget_unit f X
end AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.Test4

namespace AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.Test5
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
example (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.openRestriction f).app (laurent.op.obj X)).hom.toFunctor
      (ParameterLaurentTrack.openUnit f X) (ambientUnit P X) :=
  GlobalTensorNormalizedSupport.openRestriction_unit f X
end AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.Test5

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedTrack.Test6
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack
open GlobalTensorNormalizedSupport NaturalTrack
example (Q : Scheme.{u}) :
    ambientTrack Q = ParameterLaurentTrack.ambientTrack Q :=
  ParameterTensorNormalizedTrack.ambientTrack_eq Q
end AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedTrack.Test6

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedTrack.Test7
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
open GlobalSectionChangeIndex ParameterLaurentUnit ParameterLaurentTrack
open GlobalTensorNormalizedSupport NaturalTrack
example : supportedTrack f = ParameterLaurentTrack.supportedTrack f :=
  ParameterTensorNormalizedTrack.supportedTrack_eq f
end AlgebraicGeometry.Scheme.Modules.ParameterTensorNormalizedTrack.Test7
