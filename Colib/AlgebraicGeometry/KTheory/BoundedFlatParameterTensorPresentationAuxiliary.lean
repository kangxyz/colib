/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationActions
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentationDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialNullTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialLiftTransport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorComparisonChoice

/-! The original auxiliary-support null and localization lift on tensor ordinary presentations. -/
/-!
Implementation provenance: adapted from Quillen at
`ParameterTensorPresentationAuxiliary.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex ParameterAuxiliarySupport ParameterTensorNormalizedTrack
open SchemeTrackSequentialPresentation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The actual union-support enlargement induces the ordinary presentation map. -/
def auxiliaryEnlargement : supportedDiagram (unionOpen f T).ι ⟶ supportedDiagram T.ι :=
  ordinaryInputMap (fiber f T) (ParameterAuxiliarySupport.ambient T)
  (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual inverse-image support restriction induces the ordinary presentation map. -/
def auxiliaryRestriction : supportedDiagram T.ι ⟶ supportedDiagram (inverseOpen f T).ι :=
  ordinaryInputMap
  (ParameterAuxiliarySupport.ambient T) (openModel f T)
  (supportedTrack T.ι) (supportedTrack (inverseOpen f T).ι)
  (secondMap f T) (restriction_equivariant f T)

/-- The original auxiliary zero null, with its original time, descends to the ordinary objects. -/
def auxiliaryNull : DiagramNullHomotopy (auxiliaryEnlargement f T)
    (auxiliaryRestriction f T) :=
  ordinaryInputNull (fiber f T) (ParameterAuxiliarySupport.ambient T)
  (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι)
  (firstMap f T) (enlargement_equivariant f T)
  (openModel f T) (supportedTrack (inverseOpen f T).ι)
  (secondMap f T) (restriction_equivariant f T) (fullNull f T) (auxiliaryNull_equivariant f T)

/-- The actual auxiliary ordinary-presentation lift uses that specified original null. -/
def auxiliaryLift (X : Scheme.{u}ᵒᵖ) :
    supported (unionOpen f T).ι X ⟶ homotopyFiber ((auxiliaryRestriction f T).app X) :=
  homotopyFiberLift ((auxiliaryRestriction f T).app X) ((auxiliaryEnlargement f T).app X)
    ((auxiliaryNull f T).homotopy X)

/-- The original auxiliary null is preserved by the actual comparison at every time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationAuxiliary.lean:58"
  "adaptation" "Original tensor presentation localization with the same selected null."]
theorem auxiliaryNull_comparison (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (q : ((SchemeNaturalSeed.currentTelescope (fiberAction f T)).obj X).space n) :
    type_of% (ordinaryInputNull_comparisonOfEq
    (fiber f T) (ParameterAuxiliarySupport.ambient T) (openModel f T)
    (fiberAction f T) (supportedTrack (unionOpen f T).ι)
    (ambientAction T) (supportedTrack T.ι)
    (openAction f T) (supportedTrack (inverseOpen f T).ι)
    (supportedTrack_transport_eq (unionOpen f T).ι) (supportedTrack_transport_eq T.ι)
    (supportedTrack_transport_eq (inverseOpen f T).ι) (firstMap f T) (secondMap f T)
    (ParameterAuxiliarySupport.enlargement_equivariant f T)
    (ParameterAuxiliarySupport.restriction_equivariant f T)
    (enlargement_equivariant f T) (restriction_equivariant f T) (fullNull f T)
    (timeSlice_equivariant f T) (auxiliaryNull_equivariant f T) X n r q) :=
  ordinaryInputNull_comparisonOfEq
    (fiber f T) (ParameterAuxiliarySupport.ambient T) (openModel f T)
    (fiberAction f T) (supportedTrack (unionOpen f T).ι)
    (ambientAction T) (supportedTrack T.ι)
    (openAction f T) (supportedTrack (inverseOpen f T).ι)
    (supportedTrack_transport_eq (unionOpen f T).ι) (supportedTrack_transport_eq T.ι)
    (supportedTrack_transport_eq (inverseOpen f T).ι) (firstMap f T) (secondMap f T)
    (ParameterAuxiliarySupport.enlargement_equivariant f T)
    (ParameterAuxiliarySupport.restriction_equivariant f T)
    (enlargement_equivariant f T) (restriction_equivariant f T) (fullNull f T)
    (timeSlice_equivariant f T) (auxiliaryNull_equivariant f T) X n r q
/-- The original G7 hypotheses imply stability for this actual same-null ordinary lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationAuxiliary.lean:83"
  "adaptation" "Original tensor presentation localization with the same selected null."]
theorem auxiliaryLift_integer_isStableEquivalence
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] :
    IsStableEquivalence (auxiliaryLift f T (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) := by
  have hs := ParameterAuxiliaryCurrentFiber.currentLift_integer_isStableEquivalence f T
  dsimp only [ParameterAuxiliaryCurrentFiber.currentLift,
    currentEnlargement, currentRestriction, currentNull] at hs
  have h := ordinaryInputLift_stableOfEq
    (fiber f T) (ParameterAuxiliarySupport.ambient T) (openModel f T)
    (fiberAction f T) (supportedTrack (unionOpen f T).ι)
    (ambientAction T) (supportedTrack T.ι)
    (openAction f T) (supportedTrack (inverseOpen f T).ι)
    (supportedTrack_transport_eq (unionOpen f T).ι) (supportedTrack_transport_eq T.ι)
    (supportedTrack_transport_eq (inverseOpen f T).ι) (firstMap f T) (secondMap f T)
    (ParameterAuxiliarySupport.enlargement_equivariant f T)
    (ParameterAuxiliarySupport.restriction_equivariant f T)
    (enlargement_equivariant f T) (restriction_equivariant f T) (fullNull f T)
    (timeSlice_equivariant f T) (auxiliaryNull_equivariant f T)
    (op (Spec (CommRingCat.of (ULift.{u} ℤ)))) hs
  dsimp only [auxiliaryLift, auxiliaryNull, auxiliaryEnlargement, auxiliaryRestriction,
    supported, supportedDiagram]
  exact h

/-- Projection of the actual auxiliary lift is the original enlargement's ordinary image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationAuxiliary.lean:105"
  "adaptation" "Original tensor presentation localization with the same selected null."]
theorem auxiliaryLift_projection (X : Scheme.{u}ᵒᵖ) :
    auxiliaryLift f T X ≫ homotopyFiberProjection ((auxiliaryRestriction f T).app X) =
      (auxiliaryEnlargement f T).app X :=
  homotopyFiberLift_projection _ _ _

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation

attribute [colib_tag "COL-0600"] auxiliaryLift_integer_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
