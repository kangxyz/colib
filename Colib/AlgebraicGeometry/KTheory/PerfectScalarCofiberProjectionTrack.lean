/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSequenceMap
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Colib.Topology.Realization.HomotopyNaturality

/-!
# The same-normalization fine scalar projection cylinder

The same coarse-normalized identity and middle functors are fine exact. The actual fine
projection cylinder maps to the original coarse cylinder at every input and time. The
prespectrum inclusion and composition triangle are separate from this ordinary comparison.
No identity additivity track, right-half summand or canonical null is removed here.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberProjectionTrack.lean:37-94,
  109-133`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)

/-- The exact identity normalization used by the coarse scalar sequence. -/
def perfectOpenScalarIdentityRebaseIso :
    𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) ≅
      CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := X.toRingedSpace)))) (V).zero (W).zero
      (((hF).zero (V).isZero).iso (W).isZero) :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

variable (r : Γ(X, ⊤))
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The exact middle normalization used by the coarse scalar sequence. -/
def perfectOpenScalarMiddleRebaseIso :
    perfectScalarMiddleFunctor X r ≅
      CategoryTheory.rebaseFunctor (perfectScalarMiddleFunctor X r) (V).zero (W).zero
        (((hM).zero (V).isZero).iso (W).isZero) :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The same coarse-normalized identity functor is fine exact, with no second rebasing. -/
theorem perfectOpenScalarIdentityRebase_fineExact :
    IsExact (V).cof (V).weq (V).cof (V).weq
      (CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
        (X := X.toRingedSpace)))) (V).zero (W).zero
        (((hF).zero (V).isZero).iso (W).isZero)) :=
  (IsExact.id (V).cof (V).weq).of_iso (perfectOpenScalarIdentityRebaseIso j)

/-- The same coarse-normalized middle functor is fine exact as well. -/
theorem perfectOpenScalarMiddleRebase_fineExact :
    IsExact (V).cof (V).weq (V).cof (V).weq
      (CategoryTheory.rebaseFunctor (perfectScalarMiddleFunctor X r) (V).zero (W).zero
        (((hM).zero (V).isZero).iso (W).isZero)) :=
  (perfectScalarMiddleFunctor_waldhausenExact X r).of_iso
    (perfectOpenScalarMiddleRebaseIso j r)

/-- The unchanged projection, conjugated by exactly the two coarse endpoint normalizations. -/
theorem perfectOpenScalarNormalizedProjection_fineWeak (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (V).weq ((normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r)).app K) :=
  (V).weq.comp_mem _ _ ((V).weq_iso _ inferInstance)
    ((V).weq.comp_mem _ _ (perfectScalarProjectionNat_weak X r K)
      ((V).weq_iso _ inferInstance))

/-- The actual fine projection cylinder between the same two normalized functors. -/
def perfectOpenScalarProjectionFineRealizationHomotopy :
    (deloopingMap (perfectOpenScalarMiddleRebase_fineExact j r)).hom.Homotopy
      (deloopingMap (perfectOpenScalarIdentityRebase_fineExact j)).hom :=
  weakNaturalTransformationRealizationHomotopy V V
    (perfectOpenScalarMiddleRebase_fineExact j r)
    (perfectOpenScalarIdentityRebase_fineExact j)
    (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
    (perfectOpenScalarNormalizedProjection_fineWeak j r)

/-- The coarse projection is the original weak cylinder with its actual canonical conjugation. -/
def perfectOpenScalarProjectionRealizationHomotopy :
    (deloopingMap (hM).rebase).hom.Homotopy (deloopingMap (hF).rebase).hom :=
  weakNaturalTransformationRealizationHomotopy V W (hM).rebase (hF).rebase
    (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
    (normalizedWeakTransformation_weak hM hF (perfectScalarProjectionNat X r)
      (perfectScalarProjectionNat_openWeak j r))

/-- Fine-to-coarse transport preserves the whole projection cylinder, for all inputs and times. -/
theorem perfectOpenScalarProjectionRealizationHomotopy_changeWeak
    (t : unitInterval) (x : (V).Delooping) :
    changeWeakMap (perfectOpenNested j)
        (perfectOpenScalarProjectionFineRealizationHomotopy j r (t, x)) =
      perfectOpenScalarProjectionRealizationHomotopy j r (t, x) := by
  have h := realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy V V
      (perfectOpenScalarMiddleRebase_fineExact j r)
      (perfectOpenScalarIdentityRebase_fineExact j)
      (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
      (perfectOpenScalarNormalizedProjection_fineWeak j r))
    (weakNaturalTransformationHomotopy V W (hM).rebase (hF).rebase
      (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
      (normalizedWeakTransformation_weak hM hF (perfectScalarProjectionNat X r)
        (perfectScalarProjectionNat_openWeak j r)))
    (𝟙 _) (sSetMap hF) (by
      simp only [id_whiskerRight, Category.id_comp]
      ext n z : 4
      apply Subtype.ext
      rfl) t x
  rw [SSet.toTop.map_id] at h
  simp only [TopCat.id_app] at h
  convert h using 1 <;> rfl


end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
    "AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberProjectionTrack.lean:37-94, 109-133"
    "adaptation"
    "Fine exactness and whole realization of the unchanged normalized projection"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarProjectionFineRealizationHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarProjectionRealizationHomotopy_changeWeak
