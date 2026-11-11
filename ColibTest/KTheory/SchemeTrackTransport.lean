module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialTransport

open CategoryTheory Topology Opposite AlgebraicGeometry
open Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open KTheory.Bass KTheory.Bass.NaturalTrack KTheory.Bass.GeometricSeedCospan
open KTheory.Bass.SchemeTrackSequentialPresentation
universe u w
noncomputable section
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ)

example : (SchemeNaturalSeed.currentTelescope A).obj X ⟶ presentation M B X :=
  comparisonOfEq M A B h X
example : IsStableEquivalence (comparisonOfEq M A B h X) :=
  comparisonOfEq_stable M A B h X
