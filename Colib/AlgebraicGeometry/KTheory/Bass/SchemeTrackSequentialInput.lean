/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialPresentation

/-! Actual scheme-input squares for the prescribed sequentialization vertices and legs. -/
/-!
Implementation provenance: adapted from `Quillen/KTheory/Bass/SchemeTrackSequentialInput.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)

/-- The original whole finite Bass map of the actual scheme arrow. -/
def input (i : ℕ) : vertex squareFunctor M X i ⟶ vertex squareFunctor M Y i :=
  ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).map g

/-- The whole looped suspension map of the next original finite Bass input map. -/
def suspendedInput (i : ℕ) :
    suspendedVertex squareFunctor M X i ⟶ suspendedVertex squareFunctor M Y i :=
  parameterLoopingMap (suspensionConeMap (input M g (i + 1)))

/-- The literal backward units commute with the original finite input maps. -/
theorem unit_input (i : ℕ) :
    unit squareFunctor M X i ≫ suspendedInput M g i =
      input M g (i + 1) ≫ unit squareFunctor M Y i :=
  (suspensionLoopUnit_naturality (input M g (i + 1))).symm

/-- Every actual current-stage seed preserves the whole original scheme map. -/
theorem current_input (i : ℕ) :
    current M A X i ≫ input M g (i + 1) = input M g i ≫ current M A Y i :=
  (SchemeNaturalSeed.currentTransition A i).naturality g |>.symm

/-- The complete forward leg keeps both the original current seed and suspension-unit square. -/
theorem forward_input (i : ℕ) :
    forward M A X i ≫ suspendedInput M g i = input M g i ≫ forward M A Y i := by
  unfold forward
  rw [Category.assoc, unit_input, ← Category.assoc, current_input, Category.assoc]

end KTheory.Bass.SchemeTrackSequentialPresentation
