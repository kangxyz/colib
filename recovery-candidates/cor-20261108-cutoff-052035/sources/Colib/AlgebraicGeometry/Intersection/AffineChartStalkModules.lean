/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineStalkModules
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual stalk modules in affine charts

An actual commuting affine square identifies the actual stalk scalar action with
`Localization.localRingHom`. An actual closed immersion supplies surjectivity of
its coordinate map, so its source stalk module is the localized full coordinate
module without an assumed comparison or discarded nilpotents.

Background: Stacks Project, tags 01HR, 01HX and 00CM. Implementation provenance:
motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380, AffineClosedSupportTor
and AffineMiddleTor. This source is reconstructed from retained proof details and
interfaces; no replacement-executor validation is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- The actual scheme stalk is the localization in its specified affine chart. -/
def stalkIsoOfAffineChart (e : X ≅ Spec (.of R)) (x : X) :
    X.presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime (e.hom x).asIdeal) :=
  (asIso (e.hom.stalkMap x)).symm ≪≫ Spec.stalkIso (.of R) (e.hom x)

/-- A commuting affine square identifies the actual prime above a source point. -/
lemma affineChart_point_comap (j : Y ⟶ X)
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f)) (y : Y) :
    eX.hom (j y) = (eY.hom y).comap f :=
  congrArg (fun t : Y ⟶ Spec (.of R) => t y) h

/-- The actual chart-stalk isomorphisms conjugate the actual scalar map to localization. -/
@[reassoc]
lemma stalkMap_stalkIsoOfAffineChart_hom (j : Y ⟶ X)
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f)) (y : Y) :
    j.stalkMap y ≫ (stalkIsoOfAffineChart eY y).hom =
      (stalkIsoOfAffineChart eX (j y)).hom ≫
        CommRingCat.ofHom (Localization.localRingHom (eX.hom (j y)).asIdeal
          (eY.hom y).asIdeal f (congrArg PrimeSpectrum.asIdeal
            (affineChart_point_comap j eX eY f h y))) := by
  have hs (p : PrimeSpectrum R) (hp : p = (eY.hom y).comap f) :
      ((Spec (.of R)).presheaf.stalkCongr (.of_eq hp)).hom ≫
          (Spec.map (CommRingCat.ofHom f)).stalkMap (eY.hom y) ≫
          (Spec.stalkIso (.of S) (eY.hom y)).hom =
        (Spec.stalkIso (.of R) p).hom ≫ CommRingCat.ofHom
          (Localization.localRingHom p.asIdeal (eY.hom y).asIdeal f
            (congrArg PrimeSpectrum.asIdeal hp)) := by
    subst p
    simpa [TopCat.Presheaf.stalkCongr] using stalkMap_specStalkIso_hom f (eY.hom y)
  have hc := Hom.stalkMap_congr_hom (j ≫ eX.hom)
    (eY.hom ≫ Spec.map (CommRingCat.ofHom f)) h y
  simp only [Hom.stalkMap_comp] at hc
  apply (cancel_epi (eX.hom.stalkMap (j y))).mp
  simp only [stalkIsoOfAffineChart, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hc]
  simpa only [Category.assoc, asIso_hom, Iso.hom_inv_id_assoc] using
    hs (eX.hom (j y)) (affineChart_point_comap j eX eY f h y)

/-- The actual source stalk module is its coordinate local ring with the actual scalar map. -/
def stalkModuleIsoOfAffineChart (j : Y ⟶ X)
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f)) (y : Y) :
    (ModuleCat.restrictScalars (j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (stalkIsoOfAffineChart eX (j y)).hom.hom).obj
      ((ModuleCat.restrictScalars (Localization.localRingHom (eX.hom (j y)).asIdeal
        (eY.hom y).asIdeal f (congrArg PrimeSpectrum.asIdeal
          (affineChart_point_comap j eX eY f h y)))).obj
        (ModuleCat.of (Localization.AtPrime (eY.hom y).asIdeal)
          (Localization.AtPrime (eY.hom y).asIdeal))) := by
  let e := stalkIsoOfAffineChart eY y
  let a := (j.stalkMap y).hom
  let b := (stalkIsoOfAffineChart eX (j y)).hom.hom
  let g := Localization.localRingHom (eX.hom (j y)).asIdeal (eY.hom y).asIdeal f
    (congrArg PrimeSpectrum.asIdeal (affineChart_point_comap j eX eY f h y))
  have hc : e.hom.hom.comp a = g.comp b :=
    congrArg (fun t => t.hom) (stalkMap_stalkIsoOfAffineChart_hom j eX eY f h y)
  exact (ModuleCat.restrictScalars a).mapIso
      (ModuleCat.restrictScalarsIsoOfEquiv e.commRingCatIsoToRingEquiv).symm ≪≫
    (ModuleCat.restrictScalarsComp'App a e.hom.hom _ rfl _).symm ≪≫
    ModuleCat.restrictScalarsComp'App b g _ hc _

/-- The actual source stalk module at an explicitly equal ambient point. -/
def stalkModuleIsoOfAffineChartOfEq (j : Y ⟶ X)
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (y : Y) (x : X) (hx : x = j y) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (stalkIsoOfAffineChart eX x).hom.hom).obj
      ((ModuleCat.restrictScalars (Localization.localRingHom (eX.hom x).asIdeal
        (eY.hom y).asIdeal f (congrArg PrimeSpectrum.asIdeal
          ((congrArg eX.hom hx).trans (affineChart_point_comap j eX eY f h y))))).obj
        (ModuleCat.of (Localization.AtPrime (eY.hom y).asIdeal)
          (Localization.AtPrime (eY.hom y).asIdeal))) := by
  subst x
  simpa [TopCat.Presheaf.stalkCongr] using stalkModuleIsoOfAffineChart j eX eY f h y

/-- A surjective affine coordinate map gives the actual closed-source stalk as scalar extension. -/
def closedStalkModuleIsoOfAffineChartOfEq (j : Y ⟶ X)
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (hf : Function.Surjective f)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (y : Y) (x : X) (hx : x = j y) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (stalkIsoOfAffineChart eX x).hom.hom).obj
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))) :=
  stalkModuleIsoOfAffineChartOfEq j eX eY f h y x hx ≪≫
    (ModuleCat.restrictScalars (stalkIsoOfAffineChart eX x).hom.hom).mapIso
      (ModuleCat.extendScalarsTargetAtPrimeIsoOfEq f hf (eY.hom y) (eX.hom x)
        ((congrArg eX.hom hx).trans (affineChart_point_comap j eX eY f h y))).symm

/-- A coordinate map of an actual closed immersion is surjective. -/
lemma surjective_affineChartMap_of_isClosedImmersion (j : Y ⟶ X) [IsClosedImmersion j]
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    Function.Surjective f := by
  have hc : IsClosedImmersion (eY.hom ≫ Spec.map (CommRingCat.ofHom f)) :=
    h ▸ inferInstanceAs (IsClosedImmersion (j ≫ eX.hom))
  have hf := (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    eY.hom (Spec.map (CommRingCat.ofHom f))).mp hc
  exact (HasAffineProperty.SpecMap_iff_of_affineAnd (P := @IsClosedImmersion)
    (Q := fun f => Function.Surjective f) inferInstance RingHom.surjective_respectsIso
    (CommRingCat.ofHom f)).mp hf

/-- An actual closed immersion supplies the source-stalk comparison without assumed surjectivity. -/
def closedImmersionStalkModuleIsoOfAffineChartOfEq
    (j : Y ⟶ X) [IsClosedImmersion j]
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S)) (f : R →+* S)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (y : Y) (x : X) (hx : x = j y) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (stalkIsoOfAffineChart eX x).hom.hom).obj
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))) :=
  closedStalkModuleIsoOfAffineChartOfEq j eX eY f
    (surjective_affineChartMap_of_isClosedImmersion j eX eY f h) h y x hx

end AlgebraicGeometry.Scheme
