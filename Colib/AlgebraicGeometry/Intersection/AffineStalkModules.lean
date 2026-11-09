/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual affine stalk modules

The actual stalk map of `Spec.map f` becomes the native localized ring homomorphism
under `Spec.stalkIso`. For a surjective coordinate map, its target local ring is
also the scalar extension of the full target ring. No reduced quotient is taken.

Background: Stacks Project, tags 01HR (affine structure-sheaf stalks), 01HX
(functoriality of affine schemes), and 00CM (localization).
Implementation provenance: motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380,
AffineClosedSupportTor and AffineMiddleTor. Recovery candidate reconstructed from
retained declaration and proof details; subsequently validated in the accepted native leaf snapshot.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual affine stalk map has the native localized coordinate action. -/
@[reassoc]
lemma stalkMap_specStalkIso_hom (f : R →+* S) (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom f)).stalkMap q ≫ (Spec.stalkIso (.of S) q).hom =
      (Spec.stalkIso (.of R) (q.comap f)).hom ≫
        CommRingCat.ofHom (Localization.localRingHom
          (q.comap f).asIdeal q.asIdeal f rfl) := by
  rw [← Scheme.localRingHom_comp_stalkIso]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The actual affine source stalk, with its actual ambient scalar action. -/
def specStalkModuleIso (f : R →+* S) (q : PrimeSpectrum S) :
    (ModuleCat.restrictScalars ((Spec.map (CommRingCat.ofHom f)).stalkMap q).hom).obj
      (ModuleCat.of ((Spec (.of S)).presheaf.stalk q) ((Spec (.of S)).presheaf.stalk q)) ≅
    (ModuleCat.restrictScalars (Spec.stalkIso (.of R) (q.comap f)).hom.hom).obj
      ((ModuleCat.restrictScalars
        (Localization.localRingHom (q.comap f).asIdeal q.asIdeal f rfl)).obj
        (ModuleCat.of (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal))) := by
  let e := Spec.stalkIso (.of S) q
  let a := ((Spec.map (CommRingCat.ofHom f)).stalkMap q).hom
  let b := (Spec.stalkIso (.of R) (q.comap f)).hom.hom
  let g := Localization.localRingHom (q.comap f).asIdeal q.asIdeal f rfl
  have h : e.hom.hom.comp a = g.comp b :=
    congrArg (fun t => t.hom) (stalkMap_specStalkIso_hom f q)
  exact (ModuleCat.restrictScalars a).mapIso
      (ModuleCat.restrictScalarsIsoOfEquiv e.commRingCatIsoToRingEquiv).symm ≪≫
    (ModuleCat.restrictScalarsComp'App a e.hom.hom _ rfl _).symm ≪≫
    ModuleCat.restrictScalarsComp'App b g _ h _

/-- The affine stalk identification at an explicitly equal ambient prime. -/
def specStalkModuleIsoOfEq (f : R →+* S) (q : PrimeSpectrum S)
    (p : PrimeSpectrum R) (hp : p = q.comap f) :
    (ModuleCat.restrictScalars
      (((Spec (.of R)).presheaf.stalkCongr (.of_eq hp)).hom ≫
        (Spec.map (CommRingCat.ofHom f)).stalkMap q).hom).obj
      (ModuleCat.of ((Spec (.of S)).presheaf.stalk q) ((Spec (.of S)).presheaf.stalk q)) ≅
    (ModuleCat.restrictScalars (Spec.stalkIso (.of R) p).hom.hom).obj
      ((ModuleCat.restrictScalars (Localization.localRingHom p.asIdeal q.asIdeal f
        (congrArg PrimeSpectrum.asIdeal hp))).obj
        (ModuleCat.of (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal))) := by
  subst p
  simpa [TopCat.Presheaf.stalkCongr] using specStalkModuleIso f q

end AlgebraicGeometry.Scheme

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

local instance {T : Type u} [CommRing T] (p : Ideal T) [p.IsPrime] :
    Ring (Localization.AtPrime p) :=
  (inferInstance : CommRing (Localization.AtPrime p)).toRing

/-- For a surjective ring map, localizing the target as a source module gives its local ring. -/
def extendScalarsTargetAtPrimeIso (f : R →+* S) (hf : Function.Surjective f)
    (q : PrimeSpectrum S) :
    (extendScalars (algebraMap R (Localization.AtPrime (q.comap f).asIdeal))).obj
      ((restrictScalars f).obj (of S S)) ≅
    (restrictScalars (Localization.localRingHom (q.comap f).asIdeal q.asIdeal f rfl)).obj
      (of (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)) := by
  let p := (q.comap f).asIdeal
  let φ := algebraMap R (Localization.AtPrime p)
  have hA : φ.toAlgebra = (inferInstance : Algebra R (Localization.AtPrime p)) :=
    toAlgebra_algebraMap
  have hφ : letI := φ.toAlgebra; IsLocalization p.primeCompl (Localization.AtPrime p) := by
    rw [hA]
    infer_instance
  letI := f.toAlgebra
  letI := φ.toAlgebra
  letI : Module R (Localization.AtPrime p) := Module.compHom _ φ
  letI : SMul R (Localization.AtPrime p) := φ.toAlgebra.toSMul
  letI := hφ
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p q.asIdeal f rfl).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal)]
      exact (Localization.localRingHom_to_map p q.asIdeal f rfl r).symm)
  letI : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
      (Localization.AtPrime q.asIdeal) := by
    change IsLocalization (p.primeCompl.map f) (Localization.AtPrime q.asIdeal)
    have hm : p.primeCompl.map f = q.asIdeal.primeCompl :=
      Ideal.map_primeCompl_comap_of_surjective f hf q.asIdeal
    rw [hm]
    infer_instance
  exact (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
    (IsScalarTower.toAlgHom R S (Localization.AtPrime q.asIdeal)).toLinearMap).equiv.toModuleIso

/-- The target-localization comparison at an explicitly equal ambient prime. -/
def extendScalarsTargetAtPrimeIsoOfEq (f : R →+* S) (hf : Function.Surjective f)
    (q : PrimeSpectrum S) (p : PrimeSpectrum R) (hp : p = q.comap f) :
    (extendScalars (algebraMap R (Localization.AtPrime p.asIdeal))).obj
      ((restrictScalars f).obj (of S S)) ≅
    (restrictScalars (Localization.localRingHom p.asIdeal q.asIdeal f
      (congrArg PrimeSpectrum.asIdeal hp))).obj
      (of (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)) := by
  subst p
  exact extendScalarsTargetAtPrimeIso f hf q

end ModuleCat
