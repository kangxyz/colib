module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation

open CategoryTheory Topology Opposite AlgebraicGeometry
open Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
universe u
noncomputable section
example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ambientComparison Q X) := ambientComparison_stable Q X
example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (supportedComparison f X) := supportedComparison_stable f X
example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope (ParameterLaurentTrack.ambientTrack Q)).obj X ⟶
      ambient Q X := ambientComparison Q X
