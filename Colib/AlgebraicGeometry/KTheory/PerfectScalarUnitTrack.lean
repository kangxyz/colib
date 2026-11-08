/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarPrespectrumHomotopy
public import Colib.AlgebraicGeometry.KTheory.PerfectFlatUnitHomotopy
public import Colib.KTheory.Waldhausen.Iterated.NormalizationTrackPasting
public import Colib.KTheory.Waldhausen.Iterated.ExactPastingHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyIntertwining

/-!
# The entire normalized scalar restriction and flat-unit comparison

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarUnitTrack.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- The actual normalized open-restriction prespectrum map. -/
def perfectOpenScalarRestrictionMap :
    originalPrespectrum (perfectOpenWeakWaldhausen j) ⟶
      originalPrespectrum (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) :=
  exactOriginalPrespectrumMap _ _ (perfectOpenRestrict_isExact j)

/-- The comparison is exactly reversed normalization followed by the original geometric iso. -/
def perfectOpenRestrictionFlatHomotopy :
    Homotopy
      (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j)) ≫
        perfectOpenScalarRestrictionMap j) (perfectFlatPrespectrumMap j) :=
  (exactOriginalPrespectrumMapCompHomotopy _ _ _
    (changeWeak_exact (perfectOpenNested j)) (perfectOpenRestrict_isExact j)).symm.trans
      (exactOriginalPrespectrumIsoHomotopy _ _
        ((changeWeak_exact (perfectOpenNested j)).comp (perfectOpenRestrict_isExact j))
        (perfectFlatPullback_waldhausenExact j) (perfectOpenRestrictionFlatIso j))

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
include hq in
/-- The entire actual transformation square follows from the original termwise scalar equation. -/
theorem perfectOpenScalarRestrictionTransformation :
    Functor.whiskerRight (perfectGlobalScalar X r) (perfectComplexesRestrictOpenImmersion j) ≫
        (perfectOpenRestrictionFlatIso j).hom =
      (perfectOpenRestrictionFlatIso j).hom ≫ (perfectFlatPullbackUnitIso j q).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    perfectOpenRestrictionFlatIso, Iso.trans_hom, Functor.leftUnitor_hom_app,
    perfectFlatPullbackUnitIso, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  rw [perfectRestrict_scalar_eq_globalUnit j r q hq K]
  exact ((perfectGlobalUnitIso U q).hom.naturality
    ((perfectRestrictIsoFlatPullback j).hom.app K)).symm

/-- The specified full scalar track intertwines the actual flat-unit track along the unchanged
reversed-first normalization and forward geometric comparison. -/
def perfectOpenScalarRestrictionUnitTrack :
    (((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j)).trans
        (perfectOpenRestrictionFlatHomotopy j)).RelHomotopy
      ((perfectOpenRestrictionFlatHomotopy j).trans (perfectFlatUnitHomotopy j q)) := by
  let hF := changeWeak_exact (perfectOpenNested j)
  let hR := perfectOpenRestrict_isExact j
  let hP := perfectFlatPullback_waldhausenExact j
  let eta := perfectGlobalScalar X r
  let hEta := fun K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) =>
      quasiIso_restrict_complexGlobalScalar j r q hq K.obj
  let e := perfectOpenRestrictionFlatIso j
  let Ueta := exactOriginalPrespectrumHomotopy _ _ (hF.comp hR) (hF.comp hR)
    (Functor.whiskerRight eta (perfectComplexesRestrictOpenImmersion j)) (fun K => hR.weak _ (hEta
    K))
  let C := exactOriginalPrespectrumMapCompHomotopy _ _ _ hF hR
  let D := exactOriginalPrespectrumIsoHomotopy _ _ (hF.comp hR) hP e
  let Veta := (perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)
  let Hq := perfectFlatUnitHomotopy j q
  have JC : (Ueta.trans C).RelHomotopy (C.trans Veta) :=
    exactNormalizationLeftTrackPasting hF hF hR eta hEta
  have JD : (Ueta.trans D).RelHomotopy (D.trans Hq) :=
    exactOriginalPrespectrumPastingHomotopy _ _ (hF.comp hR) (hF.comp hR) hP hP
      (Functor.whiskerRight eta (perfectComplexesRestrictOpenImmersion j)) e.hom e.hom
      (perfectFlatPullbackUnitIso j q).hom
      (fun K => hR.weak _ (hEta K)) (fun _ => (RingedSpace.perfectComplexesWaldhausen
    U.toRingedSpace).weq_iso _ inferInstance)
      (fun _ => (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).weq_iso _ inferInstance)
      (fun _ => (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).weq_iso _ inferInstance)
      (perfectOpenScalarRestrictionTransformation j r q hq)
  exact Homotopy.RelHomotopy.intertwine C D Ueta Veta Hq JC.symm JD.symm

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarUnitTrack.lean:1-113"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarRestrictionMap
  AlgebraicGeometry.Scheme.Modules.perfectOpenRestrictionFlatHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarRestrictionTransformation
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarRestrictionUnitTrack

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarRestrictionUnitTrack
