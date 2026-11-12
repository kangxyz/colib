/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGeneratedTrace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorRecursiveCoordinates
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorBoundaryRecognition
public import Colib.KTheory.Bass.ModelRowZigzagBackwardStable
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization

/-! Integration regressions for the actual tensor construction and existing same-null localization.
These statements neither define an external TT spectrum nor assume a recognition certificate.

Adapted from `QuillenTest/TensorBassConstruction.lean` in `kangxyz/quillen-k-theory`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`,
blob `9b175d2e27b9807c280c073b82ade661d7fac552`.
The original three full statements and proofs are retained on their native owners. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.Modules.TensorConstructionLocalization
open GlobalSectionChangeIndex ReturnedTensorConeRecognition ParameterTensorEvaluationRow
  GeometricSeedCospan GlobalSupportedSection
open ModelDiagramRowInterchange GeometricSquareInterchange TensorGeneratedRecipe

/-- Every actual tensor-started finite cell has a generator-defined trace.
All naturality, endpoint, index and row data are instantiated, not hypotheses. -/
theorem generated_tensor_stages (Q : Scheme.{u}) (i : ℕ) :
    GeneratedTrace laurent.op coefficient squareFunctor
      (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ))))
      (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ)))) i (ParameterModels.ambient Q ⋙ prespectrumFunctor)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q))
      (initial_structure (ParameterModels.ambient Q))
      (NaturalTrack.ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q))
      (tensorFamily Q) (strictifiedIteratedCell Q i) :=
  tensor_generated_trace Q i

/-- The actual tensor-rooted normalized forward has the whole current-forward homotopy,
with its specified stable backward leg, at every stage and parameter scheme. -/
theorem tensor_current_roof (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Nonempty (Homotopy (strictifiedNormalizedForward Q i X)
      ((SchemeNaturalSeed.currentTransition
        (NaturalTrack.ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
          (ParameterLaurentUnit.ambientUnit Q)
          (ParameterLaurentUnit.ambientUnit_naturality Q)) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor (ParameterModels.ambient Q) X i)) ∧
    IsStableEquivalence
      (ModelRowZigzagSequentialization.backward squareFunctor (ParameterModels.ambient Q) X i) :=
  ⟨⟨tensorStageBoundaryCurrentHomotopy Q i X⟩,
    ModelRowZigzagSequentialization.backward_stable _ _ _ _⟩

/-- Both actual current-model lifts use the original support-to-open nulls.
The auxiliary open remains compact; no affine or noetherian premise is added. -/
theorem basic_auxiliary_same_null {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] :
    IsStableEquivalence (ParameterFullCurrentNull.currentLift f (op
      (Spec (CommRingCat.of (ULift.{u} ℤ))))) ∧
    IsStableEquivalence (ParameterAuxiliaryCurrentFiber.currentLift f T (op
      (Spec (CommRingCat.of (ULift.{u} ℤ))))) :=
  ⟨ParameterFullCurrentNull.currentLift_integer_isStableEquivalence f,
    ParameterAuxiliaryCurrentFiber.currentLift_integer_isStableEquivalence f T⟩

end AlgebraicGeometry.Scheme.Modules.TensorConstructionLocalization
