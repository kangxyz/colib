/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarPrespectrumHomotopy
public import Colib.KTheory.Waldhausen.Fibration.Prespectrum
public import Colib.KTheory.Waldhausen.Iterated.HomotopyTransport
public import Colib.KTheory.Waldhausen.Iterated.NormalizationPasting

/-!
# Actual raw-to-normalized scalar tracks

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarUnitTrackTransport.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- The specified raw change-weak map is joined to its actual canonical zero rebase. -/
def perfectOpenChangeWeakNormalizationHomotopy :
    Homotopy (changeWeakPrespectrumMap (perfectOpenNested j))
      (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j))) :=
  originalPrespectrumTransformationHomotopy _ _ (changeWeak_exact (perfectOpenNested j))
    (changeWeak_exact (perfectOpenNested j)).rebase
    (perfectOpenNested j).zero_eq.symm (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctorIso (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).zero
      (perfectOpenWeakWaldhausen j).zero
      (((changeWeak_exact (perfectOpenNested j)).zero (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace).isZero).iso
        (perfectOpenWeakWaldhausen j).isZero)).hom
    (fun _ => (perfectOpenWeakWaldhausen j).weq_iso _ inferInstance)
variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
/-- The original scalar cylinder is used without any additional zero rebasing. -/
def perfectOpenScalarOriginalHomotopy :
    Homotopy (changeWeakPrespectrumMap (perfectOpenNested j))
      (changeWeakPrespectrumMap (perfectOpenNested j)) :=
  originalPrespectrumTransformationHomotopy _ _ (changeWeak_exact (perfectOpenNested j))
    (changeWeak_exact (perfectOpenNested j)) (perfectOpenNested j).zero_eq.symm
    (perfectOpenNested j).zero_eq.symm (perfectGlobalScalar X r)
    (fun K => quasiIso_restrict_complexGlobalScalar j r q hq K.obj)

/-- The full original raw and rebased scalar tracks intertwine along the actual rebase track. -/
def perfectOpenScalarNormalizationTrack :
    ((perfectOpenScalarOriginalHomotopy j r q hq).trans
      (perfectOpenChangeWeakNormalizationHomotopy j)).RelHomotopy
    ((perfectOpenChangeWeakNormalizationHomotopy j).trans
      (perfectOpenScalarPrespectrumHomotopy j r q hq)) := by
  let h := changeWeak_exact (perfectOpenNested j)
  let e := CategoryTheory.rebaseFunctorIso (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).zero
    (perfectOpenWeakWaldhausen j).zero
    ((h.zero (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero).iso
    (perfectOpenWeakWaldhausen j).isZero)
  let eta := perfectGlobalScalar X r
  let hEta := fun K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) =>
      quasiIso_restrict_complexGlobalScalar j r q hq K.obj
  have he : eta ≫ e.hom = e.hom ≫ normalizedWeakTransformation h h eta := by
    change eta ≫ e.hom = e.hom ≫ (e.inv ≫ eta ≫ e.hom)
    simp only [Iso.hom_inv_id_assoc]
  exact originalPrespectrumPastingHomotopy _ _ h h h.rebase h.rebase
    (perfectOpenNested j).zero_eq.symm (perfectOpenNested j).zero_eq.symm
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    eta e.hom e.hom (normalizedWeakTransformation h h eta) hEta
    (fun _ => (perfectOpenWeakWaldhausen j).weq_iso _ inferInstance)
    (fun _ => (perfectOpenWeakWaldhausen j).weq_iso _ inferInstance)
    (normalizedWeakTransformation_weak h h eta hEta) he

/-- Every point of the entire raw level-one scalar track is the old realization cylinder. -/
theorem perfectOpenScalarOriginalHomotopy_level_one (s : unitInterval)
    (x : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).Delooping) :
    (perfectOpenScalarOriginalHomotopy j r q hq).level 1
        (s, (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).asSmallDeloopingHomeomorph x) =
      (perfectOpenWeakWaldhausen j).asSmallDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)
          (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
          (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
          (fun K => quasiIso_restrict_complexGlobalScalar j r q hq K.obj) (s, x)) :=
  originalPrespectrumTransformationHomotopy_level_one _ _ _ _ _ _ _ _ s x

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarUnitTrackTransport.lean:1-126"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenChangeWeakNormalizationHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizationTrack
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalHomotopy_level_one

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizationTrack
