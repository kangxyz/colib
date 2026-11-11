/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelZigzagComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentTransition
public import Colib.Topology.Prespectrum.ZigzagSequentializationColimit

/-! Actual ordinary pushout-sequence colimits for whole tracks on Model diagrams. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ)

/-- The given whole track determines the current original finite transition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:25"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def current (i : ℕ) : vertex squareFunctor M X i ⟶ vertex squareFunctor M X (i + 1) :=
  (SchemeNaturalSeed.currentTransition A i).app X

/-- The forward leg retains that actual current seed and the original suspension unit. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:29"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def forward (i : ℕ) : vertex squareFunctor M X i ⟶ suspendedVertex squareFunctor M X i :=
  current M A X i ≫ unit squareFunctor M X i

/-- This specified forward leg has its actual whole constant factorization track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:33"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def factorization (i : ℕ) : Topology.LoopPrespectrum.Homotopy (forward M A X i)
    (current M A X i ≫ unit squareFunctor M X i) :=
  Topology.LoopPrespectrum.Homotopy.refl _

/-- The ordinary colimit of the actual canonical homotopy-pushout sequentialization. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:38"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def presentation : LoopPrespectrum.{w} :=
  ZigzagSequentialization.ordinaryColimit (vertex squareFunctor M X)
    (suspendedVertex squareFunctor M X) (forward M A X) (unit squareFunctor M X)

/-- The original current telescope maps through actual pushouts to this ordinary colimit. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:43"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def comparison : Telescope.prespectrum (vertex squareFunctor M X) (current M A X) ⟶
    presentation M A X :=
  ZigzagSequentialization.telescopeMap (vertex squareFunctor M X)
    (suspendedVertex squareFunctor M X) (forward M A X) (unit squareFunctor M X)
    (current M A X) (factorization M A X) ≫
      ZigzagSequentialization.telescopeToOrdinaryColimit (vertex squareFunctor M X)
        (suspendedVertex squareFunctor M X) (forward M A X) (unit squareFunctor M X)

/-- Original finite Model topology proves stability without any additional analytic premise. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:52"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparison_stable : IsStableEquivalence (comparison M A X) := by
  let : ∀ i n, T1Space ((vertex squareFunctor M X i).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space squareFunctor i M X n
  let : ∀ i n, T1Space ((suspendedVertex squareFunctor M X i).space n) :=
    fun i n => ModelDiagramSuspension.spaceT1Space squareFunctor (i + 1) M X n
  exact (ModelZigzagSequentialization.telescopeMap_isStableEquivalence
    squareFunctor M X (forward M A X) (current M A X) (factorization M A X)).comp
    (ZigzagSequentialization.telescopeToOrdinaryColimit_isStableEquivalence
      (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
      (forward M A X) (unit squareFunctor M X))

/-- The complete initial leg is the original first forward arrow followed by the colimit leg. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeTrackSequentialPresentation.lean:64"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem initial_leg :
    Telescope.inclusion (vertex squareFunctor M X) (current M A X) 0 ≫ comparison M A X =
      ZigzagSequentialization.initialColimitMap (vertex squareFunctor M X)
        (suspendedVertex squareFunctor M X) (forward M A X) (unit squareFunctor M X) := by
  unfold comparison presentation
  rw [← Category.assoc, ZigzagSequentialization.inclusion_telescopeMap]
  simp only [ZigzagSequentialization.comparison_zero]
  exact ZigzagSequentialization.initial_inclusion_telescopeToOrdinaryColimit _ _ _ _

end KTheory.Bass.SchemeTrackSequentialPresentation
