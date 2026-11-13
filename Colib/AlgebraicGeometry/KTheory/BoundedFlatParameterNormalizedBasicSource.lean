/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicDiagram
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryBasicCurrent
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryBottomSource
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedInputIdentity

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicSource.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The literal original source cast on normalized basic rows -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
open GlobalSupportedSection GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterLaurentTrack

private theorem normalizedInputMap_open_eq (Q : Scheme.{u}) {U V : Q.Opens} (h : U = V)
    (hη : ∀ Y, Preserves
      ((eqToHom (congrArg (fun W : Q.Opens => ParameterModels.supported W.ι) h)).app
        (laurent.op.obj Y)).hom.toFunctor (supportedUnit U.ι Y) (supportedUnit V.ι Y))
    (X : Scheme.{u}ᵒᵖ) :
    SchemeModelRowSeed.normalizedInputMap
        (ParameterModels.supported U.ι) (supportedUnit U.ι) (supportedUnit_naturality U.ι)
        (ParameterModels.supported V.ι) (supportedUnit V.ι) (supportedUnit_naturality V.ι)
        (eqToHom (congrArg (fun W : Q.Opens => ParameterModels.supported W.ι) h)) hη X =
      (eqToIso (congrArg
        (fun W : Q.Opens => ParameterTensorNormalizedRowPresentation.supported W.ι X) h)).hom := by
  cases h
  exact SchemeModelRowSeed.normalizedInputMap_id
    (ParameterModels.supported U.ι) (supportedUnit U.ι) (supportedUnit_naturality U.ι) hη X

/-- The actual original union-to-basic map acts on the independently normalized row. -/
def normalizedToBasic {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    normalizedFiberPresentation f T X ⟶ ParameterTensorNormalizedRowPresentation.supported f X :=
  SchemeModelRowSeed.normalizedInputMap
    (fiber f T) (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
    (ParameterModels.supported f) (supportedUnit f) (supportedUnit_naturality f)
    (toBasic f T) (supportedMap_unit (vanishingPair f T)) X

/-- The complete normalized comparison retains the original current union-to-basic map. -/
@[reassoc]
theorem currentToBasic_normalized_square {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    (currentToBasic f T).app X ≫ ParameterTensorNormalizedRowPresentation.supportedComparison f X =
      normalizedFiberPresentationComparison f T X ≫ normalizedToBasic f T X :=
  SchemeModelRowSeed.normalizedComparison_inputMap
    (fiber f T) (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
    (ParameterModels.supported f) (supportedUnit f) (supportedUnit_naturality f)
    (toBasic f T) (supportedMap_unit (vanishingPair f T)) X

/-- At the bottom auxiliary open, the actual normalized input is precisely the original cast. -/
theorem normalizedToBasic_bottom (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    normalizedToBasic U.ι ⊥ X = (basicSourceIso Q U X).hom := by
  let h := basic_union_eq Q U
  have he := toBasic_ι_bot_eqToHom U h
  let hη : ∀ Y, Preserves
      ((eqToHom (congrArg (fun W : Q.Opens => ParameterModels.supported W.ι) h)).app
        (laurent.op.obj Y)).hom.toFunctor
      (supportedUnit (unionOpen U.ι ⊥).ι Y) (supportedUnit U.ι Y) := fun Y => by
    rw [← he]
    exact supportedMap_unit (vanishingPair U.ι ⊥) Y
  exact (SchemeModelRowSeed.normalizedInputMap_congr
    (fiber U.ι ⊥) (supportedUnit (unionOpen U.ι ⊥).ι)
    (supportedUnit_naturality (unionOpen U.ι ⊥).ι)
    (ParameterModels.supported U.ι) (supportedUnit U.ι) (supportedUnit_naturality U.ι)
    (toBasic U.ι ⊥) (supportedMap_unit (vanishingPair U.ι ⊥))
    (eqToHom (congrArg (fun W : Q.Opens => ParameterModels.supported W.ι) h)) hη he X).trans
      (normalizedInputMap_open_eq Q h hη X)

/-- The explicit basic source cast retains the actual original current source comparison. -/
@[reassoc]
theorem currentToBasic_sourceIso_square (Q : Scheme.{u}) (U : Q.Opens)
    (X : Scheme.{u}ᵒᵖ) :
    (currentToBasic U.ι ⊥).app X ≫ ParameterTensorNormalizedRowPresentation.supportedComparison
        U.ι X =
      normalizedFiberPresentationComparison U.ι ⊥ X ≫ (basicSourceIso Q U X).hom := by
  rw [currentToBasic_normalized_square, normalizedToBasic_bottom]

end AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
