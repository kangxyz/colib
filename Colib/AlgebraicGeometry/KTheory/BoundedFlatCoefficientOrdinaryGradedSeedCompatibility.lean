/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenNull
public import Colib.KTheory.Waldhausen.Iterated.DiagramNullIdentityAction

/-! # Original ordinary graded Laurent seed and whole compatibility

Only the assigned ordinary declarations are migrated. There is no auxiliary support T.
Actual original models, selected zero, scalar/null times and seed squares are preserved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Opposite
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso



/-- The identity change of weakness retains the same original forward unit literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:80"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGrading_laurentUnit (a : Under R) :
    Preserves
      ((boundedAboveFlatCoefficientOpenGradingModelTransformation f).app
        ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((boundedAboveFlatCoefficientFullOpenLaurentAction f).unit a)
      ((boundedAboveFlatCoefficientGradedOpenLaurentAction f).unit a) := fun _ => rfl

/-- Original grading preserves every level and the same full Laurent-action time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:88"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGrading_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedAboveFlatCoefficientFullOpenLaurentHomotopy f a).level n (t, x)) =
      (boundedAboveFlatCoefficientGradedOpenLaurentHomotopy f a).level n
        (t, ((boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedAboveFlatCoefficientFullOpenLaurentAction f)
    (boundedAboveFlatCoefficientGradedOpenLaurentAction f)
    (boundedAboveFlatCoefficientOpenGradingModelTransformation f)
    (boundedAboveFlatCoefficientOpenGrading_laurentUnit f) a n t x

/-- The actual coefficient-natural grading preserves the entire original Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:102"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientFullOpenBassSeed_grading :
    boundedAboveFlatCoefficientFullOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f) =
      boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f ≫
        boundedAboveFlatCoefficientGradedOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientFullOpenLaurentAction f).track
    (boundedAboveFlatCoefficientGradedOpenLaurentAction f).track
    (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenGrading_laurent_apply f)

/-- The original zero-to-image realization supplies whole identity-action interchange. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:114"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedAboveFlatCoefficientOpenRestrictionModelTransformation f).app a)
      ((boundedAboveFlatCoefficientOpenGradingModelTransformation f).app a)
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedAboveFlatCoefficientOpenRestrictionModelTransformation f).app a)
    ((boundedAboveFlatCoefficientOpenGradingModelTransformation f).app a)
    (boundedAboveFlatCoefficientOpenZeroToGraded f a)
    (boundedAboveFlatCoefficientOpenZeroToGraded_weak f a)

/-- The actual restriction and identity grading preserve every original coefficient unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:126"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenComposite_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves
      (((boundedAboveFlatCoefficientOpenRestrictionModelTransformation f).app a ≫
        (boundedAboveFlatCoefficientOpenGradingModelTransformation f).app a).hom.toFunctor)
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a)
        (boundedAboveFlatCoefficientUnit (op Q, a) r))
      (boundedAboveFlatCoefficientSectionUnitIso (op P, a)
        (boundedAboveFlatCoefficientUnit (op P, a) r)) := by
  change Preserves (boundedAboveFlatCoefficientOpenRestriction f a ⋙ 𝟭 _) _ _
  simpa only [Functor.comp_id, boundedAboveFlatCoefficientOpenRestriction] using
    boundedAboveFlatCoefficientSectionsRestriction_unit_preserves f a r

/-- The same canonical null interchanges with the actual forward coefficient units. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:140"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedAboveFlatCoefficientOpenModelFunctor f).obj a)
      (T := (boundedAboveFlatCoefficientGradedOpenModelFunctor f).obj a)
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a)
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a)
        (boundedAboveFlatCoefficientUnit (op Q, a) r))
      (boundedAboveFlatCoefficientSectionUnitIso (op P, a)
        (boundedAboveFlatCoefficientUnit (op P, a) r)) :=
  boundedAboveFlatCoefficientOpenGradingNull_unitCompatible f a _ _
    (boundedAboveFlatCoefficientOpenComposite_unit_preserves f a r)

/-- Scalar and canonical-null times are independent on the two original Laurent tracks. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:154"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a)
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientOpenLaurentHomotopy f a)
      (boundedAboveFlatCoefficientGradedOpenLaurentHomotopy f a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedAboveFlatCoefficientOpenRestrictionModelTransformation f)
    (q := boundedAboveFlatCoefficientOpenGradingModelTransformation f)
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f) ((laurentUnderCoefficient R).app a)
    ((boundedAboveFlatCoefficientOpenLaurentAction f).unit a)
    ((boundedAboveFlatCoefficientGradedOpenLaurentAction f).unit a)
    (by
      simpa only [boundedAboveFlatCoefficientOpenLaurentAction,
        boundedAboveFlatCoefficientGradedOpenLaurentAction,
          boundedAboveFlatCoefficientSectionLaurentUnitIso]
        using boundedAboveFlatCoefficientOpenGradingNull_unitInterchange f
          ((laurentUnderFunctor R).obj a) (laurentCoordinate a.right))

/-- Each time slice of the same canonical null remains an original coefficient transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:174"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientOpenGradingNullTimeSlice (s : unitInterval) :
    boundedAboveFlatCoefficientOpenPrespectrumFunctor f ⟶
      boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f :=
  diagramHomotopyAt
    (η := boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
      boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (θ := diagramZeroMap (boundedAboveFlatCoefficientOpenPrespectrumFunctor f)
      (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f))
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f).naturality s

/-- Every time of the original canonical null satisfies the actual original seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:186"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingNullTimeSlice_seed (s : unitInterval) :
    boundedAboveFlatCoefficientOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s) =
      boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s ≫
        boundedAboveFlatCoefficientGradedOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedAboveFlatCoefficientOpenLaurentAction f).track
    (boundedAboveFlatCoefficientGradedOpenLaurentAction f).track
    (boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s)
    (fun a n t x => boundedAboveFlatCoefficientOpenGradingNull_laurentInterchange f a n s t x)

/-- The Bass image of the same canonical null, on the actual original coefficient squares. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:198"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientOpenGradingBassNullHomotopy (a : Under R) :=
  strictDiagramNullHomotopy
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f).naturality
    (laurentUnderSquareFunctor R) a

/-- The Bass null retains the same original natural time-slice map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:207"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_at (a : Under R) (s : unitInterval) :
    (boundedAboveFlatCoefficientOpenGradingBassNullHomotopy f a).at s =
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientOpenGradingNullTimeSlice f s)).app a :=
  strictDiagramMapHomotopy_at
    (η := boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
      boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (θ := diagramZeroMap (boundedAboveFlatCoefficientOpenPrespectrumFunctor f)
      (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f))
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy
    (boundedAboveFlatCoefficientOpenGradingDiagramNull f).naturality (laurentUnderSquareFunctor R)
      a s

/-- The canonical null and original seeds commute as complete based-loop values. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:220"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_seed
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    (boundedAboveFlatCoefficientOpenGradingBassNullHomotopy f a).level n
      (s, (boundedAboveFlatCoefficientOpenBassSeedMap f a).map n x) =
      (boundedAboveFlatCoefficientGradedOpenBassSeedMap f a).map n
        (((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x)) := by
  have hs := congrArg (fun g => g.map n
    ((boundedAboveFlatCoefficientOpenBassSeedMap f a).map n x))
    (boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_at f a s)
  exact hs.trans (congrArg (fun g => (g.app a).map n x)
    (boundedAboveFlatCoefficientOpenGradingNullTimeSlice_seed f s))

/-- Null time and output-loop coordinate remain independent in the exact original seed equation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenSeedCompatibility.lean:234"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_seed_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    Path.toContinuousMap ((boundedAboveFlatCoefficientOpenGradingBassNullHomotopy f a).level n
      (s, (boundedAboveFlatCoefficientOpenBassSeedMap f a).map n x)) t =
      Path.toContinuousMap ((boundedAboveFlatCoefficientGradedOpenBassSeedMap f a).map n
        (((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x))) t :=
  congrArg (fun p => Path.toContinuousMap p t)
    (boundedAboveFlatCoefficientOpenGradingBassNullHomotopy_seed f a n s x)

end AlgebraicGeometry.Scheme.Modules
