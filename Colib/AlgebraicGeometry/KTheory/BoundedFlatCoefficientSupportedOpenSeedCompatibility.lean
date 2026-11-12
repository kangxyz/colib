/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradingNull
public import Colib.KTheory.Waldhausen.Iterated.DiagramNullIdentityAction


/-!
# Actual auxiliary-supported seed squares and canonical whole-null compatibility

Supported restriction retains the original coefficient unit through the true
support square. Identity grading keeps the same supported open unit. Their
whole action tracks prove the original r_Z and q_Z Bass seed equations.

The same reversed zero-to-image null has identity-action interchange with
these supported scalar lifts. Scalar time, null time and output-loop coordinate
remain independent, and every actual null time slice preserves the same seed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

omit [IsOpenImmersion f.left] in
/-- The actual restriction preserves each original forward Laurent-unit component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:44"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_laurentUnit (a : Under R) :
    Preserves
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app
        ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).unit a)
      ((boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).unit a) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_laurentUnit_preserves f T a

omit [IsOpenImmersion f.left] in
/-- Original native restriction preserves every level and the same Laurent-action time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:54"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedAboveFlatCoefficientSupportedOpenLaurentHomotopy f T a).level n (t, x)) =
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentHomotopy f T a).level n
        (t, ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app
          a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T)
    (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T)
    (boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenRestriction_laurentUnit f T) a n t x

omit [IsOpenImmersion f.left] in
/-- The actual coefficient-natural original restriction preserves the entire original Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:70"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenBassSeed_restriction :
    boundedAboveFlatCoefficientSupportedOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) =
      boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenRestriction_laurent_apply f T)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The identity change of weakness retains the same original forward unit literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:84"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGrading_laurentUnit (a : Under R) :
    Preserves
      ((boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app
        ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).unit a)
      ((boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).unit a) := fun _ => rfl

/-- Original grading preserves every level and the same full Laurent-action time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:92"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGrading_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedAboveFlatCoefficientSupportedFullOpenLaurentHomotopy f T a).level n (t, x)) =
      (boundedAboveFlatCoefficientSupportedGradedOpenLaurentHomotopy f T a).level n
        (t, ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app
          a).map
          n x) :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction
    f T)
    (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGrading_laurentUnit f T) a n t x

/-- The actual coefficient-natural grading preserves the entire original Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:107"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedFullOpenBassSeed_grading :
    boundedAboveFlatCoefficientSupportedFullOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T) =
      boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T ≫
        boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f
    T).track
    (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGrading_laurent_apply f T)

/-- The original zero-to-image realization supplies whole identity-action interchange. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:119"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app a)
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app a)
    (boundedAboveFlatCoefficientSupportedOpenZeroToGraded f T a)
    (boundedAboveFlatCoefficientSupportedOpenZeroToGraded_weak f T a)

/-- The actual restriction and identity grading preserve every original coefficient unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:131"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenComposite_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves
      (((boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app
          a).hom.toFunctor)
      (boundedAboveFlatCoefficientSupportSectionUnitIso (boundedAboveFlatCoefficientSupportOpen Q
        T a).ι r)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι r) := by
  change Preserves (boundedAboveFlatCoefficientSupportedOpenRestriction f T a ⋙ 𝟭 _) _ _
  simpa only [Functor.comp_id] using
    boundedAboveFlatCoefficientSupportedOpenRestriction_coefficientUnit_preserves f T a r

/-- The same canonical null interchanges with the actual forward coefficient units. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:144"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T).obj a)
      (T := (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).obj a)
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)
      (boundedAboveFlatCoefficientSupportSectionUnitIso (boundedAboveFlatCoefficientSupportOpen Q
        T a).ι r)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι r) :=
  boundedAboveFlatCoefficientSupportedOpenGradingNull_unitCompatible f T a _ _
    (boundedAboveFlatCoefficientSupportedOpenComposite_unit_preserves f T a r)

/-- Scalar and canonical-null times are independent on the two original Laurent tracks. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:157"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientSupportedOpenLaurentHomotopy f T a)
      (boundedAboveFlatCoefficientSupportedGradedOpenLaurentHomotopy f T a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    (q := boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T) ((laurentUnderCoefficient
      R).app a)
    ((boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).unit a)
    ((boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).unit a)
    (by
      simpa only [boundedAboveFlatCoefficientSupportedOpenLaurentAction,
        boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction,
        boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso,
        boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso,
        boundedAboveFlatCoefficientSupportSectionUnitIso,
          boundedAboveFlatCoefficientSectionLaurentUnitIso]
        using boundedAboveFlatCoefficientSupportedOpenGradingNull_unitInterchange f T
          ((laurentUnderFunctor R).obj a) (laurentCoordinate a.right))

/-- Each time slice of the same canonical null remains an original coefficient transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:180"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T :=
  diagramHomotopyAt
    (η := boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T)
      (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality s

/-- Every time of the original canonical null satisfies the actual original seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:192"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice_seed (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice f T s) =
      boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice f T s ≫
        boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).track
    (boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice f T s)
    (fun a n t x => boundedAboveFlatCoefficientSupportedOpenGradingNull_laurentInterchange f T a n
      s t x)

/-- The Bass image of the same canonical null, on the actual original coefficient squares. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:204"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy (a : Under R) :=
  strictDiagramNullHomotopy
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality
    (laurentUnderSquareFunctor R) a

/-- The Bass null retains the same original natural time-slice map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:213"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy_at (a : Under R) (s :
  unitInterval) :
    (boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy f T a).at s =
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice f T s)).app a :=
  strictDiagramMapHomotopy_at
    (η := boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T)
      (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality
      (laurentUnderSquareFunctor R) a s

/-- The canonical null and original seeds commute as complete based-loop values. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:228"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    (boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy f T a).level n
      (s, (boundedAboveFlatCoefficientSupportedOpenBassSeedMap f T a).map n x) =
      (boundedAboveFlatCoefficientSupportedGradedOpenBassSeedMap f T a).map n
        (((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s,
          x))
          := by
  have hs := congrArg (fun g => g.map n
    ((boundedAboveFlatCoefficientSupportedOpenBassSeedMap f T a).map n x))
    (boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy_at f T a s)
  exact hs.trans (congrArg (fun g => (g.app a).map n x)
    (boundedAboveFlatCoefficientSupportedOpenGradingNullTimeSlice_seed f T s))

/-- Null time and output-loop coordinate remain independent in the exact original seed equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenSeedCompatibility.lean:243"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    Path.toContinuousMap ((boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy f T
      a).level n
      (s, (boundedAboveFlatCoefficientSupportedOpenBassSeedMap f T a).map n x)) t =
      Path.toContinuousMap ((boundedAboveFlatCoefficientSupportedGradedOpenBassSeedMap f T a).map n
        (((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s,
          x))) t :=
  congrArg (fun p => Path.toContinuousMap p t)
    (boundedAboveFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed f T a n s x)

end AlgebraicGeometry.Scheme.Modules

