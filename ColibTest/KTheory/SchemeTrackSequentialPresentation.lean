module
import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialPresentation

open CategoryTheory Topology Opposite AlgebraicGeometry
open Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open KTheory.Bass KTheory.Bass.NaturalTrack KTheory.Bass.GeometricSeedCospan
open KTheory.Bass.ModelZigzagSequentialization KTheory.Bass.SchemeTrackSequentialPresentation
universe u w
noncomputable section
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ)

example : IsStableEquivalence (comparison M A X) := comparison_stable M A X
example : Telescope.inclusion (vertex squareFunctor M X) (current M A X) 0 ≫
    comparison M A X = ZigzagSequentialization.initialColimitMap
      (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
      (forward M A X) (unit squareFunctor M X) := initial_leg M A X
example (i : ℕ) : forward M A X i = current M A X i ≫ unit squareFunctor M X i := rfl
